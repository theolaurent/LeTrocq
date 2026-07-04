/-
Classifying `@[trocq]`-tagged witnesses by their type.

A tagged constant `w` is one of four kinds, read off the conclusion of its (telescoped) type:
  • BASE       `w : Param m n A B`      (A,B closed consts, no binders)  — an equivalence of types.
  • RELATOR    `w : ∀ …, Param m n (P …) (P' …)`                        — relates an applied head `P`.
  • TYPEFORMER `w : ∀ params, F args → F' args' → Sort`  (concl a SORT) — the parametricity RELATION of a
                parameterized type `F` (e.g. `List`/`Option`); its two head constants give `⟨·⟩` the
                counterpart `F ↦ F'`. Its constructors/recursor register separately as TERM primitives.
  • TERM       `w : ∀ …, R … (c …) (c' …)`  (R a bare relation)        — relates a term head `c ↦ c'`.

The per-surface builders (`Solver.buildAtomPairs`/`buildConsts`, `Translate.buildCtx`) consume these. The
`@[trocq]` attribute (`Attr.lean`) runs `parseEntry` eagerly and stores the resulting `RegKind`.
-/
import LeTrocq.Hierarchy
import Lean
open Lean Lean.Meta
namespace LeTrocq

/-- install a registered witness in BOTH directions, keyed by head: the forward entry at `hA` always, and a
    backward entry at the B-side head `hB?` only when it is present and DISTINCT from `hA`. A homogeneous head
    (`hB? = none` or `some hA` — e.g. a polymorphic constructor `List.cons ↦ List.cons`) needs no backward
    entry: its forward witness already serves both directions (it is polymorphic in the direction-carrying
    relation), and a second entry under the same key would clobber it. The backward value is a thunk, run only
    when actually inserted. This is the single home of the forward/backward + homogeneous-skip POLICY that the
    solver (`buildAtomPairs`) and the translation (`buildCtx`) both consume; the value type `α` differs per map. `insertBidirPair` is the pair-indexed sibling (nested `srcHead ↦ tgtHead ↦ α` + a preferred-target map). -/
def insertBidir {α} (m : NameMap α) (hA : Name) (hB? : Option Name)
    (fwd : α) (bwd : MetaM α) : MetaM (NameMap α) := do
  let m := m.insert hA fwd
  match hB? with
  | some hB => if hB == hA then return m else return m.insert hB (← bwd)
  | none    => return m

/-- pair-indexed sibling of `insertBidir`: install a witness in a NESTED map `srcHead ↦ tgtHead ↦ α`
    (so several registrations for one source no longer clobber), and record the PREFERRED (last-registered)
    target head in `pref` — the synth default when no target is demanded. Same forward/backward +
    homogeneous-skip policy as `insertBidir`: forward `[hA][hB] := fwd` and `pref[hA] := hB` always; the
    backward `[hB][hA] := bwd`, `pref[hB] := hA` only when `hB` is present and DISTINCT from `hA`. -/
def insertBidirPair {α} (m : NameMap (NameMap α)) (pref : NameMap Name)
    (hA : Name) (hB? : Option Name) (fwd : α) (bwd : MetaM α) :
    MetaM (NameMap (NameMap α) × NameMap Name) := do
  let hB := hB?.getD hA
  let innerA : NameMap α := (m.find? hA).getD (mkNameMap _)
  let m : NameMap (NameMap α) := m.insert hA (innerA.insert hB fwd)
  let pref : NameMap Name := pref.insert hA hB
  if hB == hA then return (m, pref)
  let innerB : NameMap α := (m.find? hB).getD (mkNameMap _)
  let m : NameMap (NameMap α) := m.insert hB (innerB.insert hA (← bwd))
  return (m, pref.insert hB hA)

/-- the abstraction-theorem TRIPLE convention: a registered witness's binders come in groups of three,
    `(a, a', aR)` — the A-value, the B-value, and their relatedness. Check `xs.size` is a multiple of 3
    (the error names `what`/`wit`) and return the triples in order. The single home of the `3·j` indexing
    that the solver (`relatorArgKinds`) and the translation (`symPrimitive`) both walk. -/
def chunkTriples (what : String) (wit : Expr) (xs : Array Expr) : MetaM (Array (Expr × Expr × Expr)) := do
  unless xs.size % 3 == 0 do
    throwError "trocq: {what} is not in abstraction-theorem triple form ({xs.size} binders): {wit}"
  let mut ts := #[]
  for j in [0 : xs.size / 3] do
    ts := ts.push (xs[3*j]!, xs[3*j+1]!, xs[3*j+2]!)
  return ts

/-- read a `MapClass` constructor out of its `Expr`. -/
def exprToMapClass (e : Expr) : MetaM MapClass := do
  match e.getAppFn.constName? with
  | some ``MapClass.map0  => return .map0
  | some ``MapClass.map1  => return .map1
  | some ``MapClass.map2a => return .map2a
  | some ``MapClass.map2b => return .map2b
  | some ``MapClass.map3  => return .map3
  | some ``MapClass.map4  => return .map4
  | _ => throwError "trocq: cannot read a map class from {e}"

/-- the classification of a `@[trocq]` witness. The witness itself is kept as its NAME (`witName`), not a
    baked `mkConst`: consumers re-create it with fresh universe levels (`mkConstWithFreshMVarLevels`), so
    universe-polymorphic witnesses register and instantiate correctly. -/
inductive RegKind
  | base       (headA headB : Name) (tyA tyB : Expr) (witName : Name) (cls : ParamClass)
  -- a RELATOR is always GRADED: its first two binders are `(m n : MapClass)` and the conclusion is
  -- `Param m n (F …) (F' …)`, so its per-argument classes VARY with the demanded output class (the variance
  -- mechanism). The driver reads them by specializing the witness to the demand, so no class is stored here.
  | relator    (headA : Name) (headB? : Option Name) (witName : Name)
  | typeFormer (headA headB : Name) (relName : Name)
  | term       (headA : Name) (bTerm : Expr) (witName : Name)
  deriving Inhabited

/-- classify a tagged constant `w` from its type (see the kinds above). The const is built with its own
    level params (`mkConstWithLevelParams`) so a universe-polymorphic `w` telescopes without a level error. -/
def parseEntry (w : Name) : MetaM RegKind := do
  let wit ← mkConstWithLevelParams w
  forallTelescopeReducing (← inferType wit) fun bs concl => do
    let args := concl.getAppArgs
    if concl.isSort then
      -- a RELATION FORMER `F-args → F'-args' → Sort`: the parametricity relation of a parameterized type.
      -- The telescope eats the two related objects too, so they are the last two binders; their head
      -- constants name the A-/B-side type formers (equal for a homogeneous type like `List`/`Option`).
      unless bs.size ≥ 2 do throwError "trocq: type former {w} must relate two objects"
      let some hA := (← inferType bs[bs.size - 2]!).getAppFn.constName?
        | throwError "trocq: type former {w} A-object has no head constant"
      let some hB := (← inferType bs[bs.size - 1]!).getAppFn.constName?
        | throwError "trocq: type former {w} B-object has no head constant"
      return .typeFormer hA hB w
    else if concl.getAppFn.isConstOf ``Param then
      -- a GRADED relator opens with `(m n : MapClass)` and concludes `Param m n (F …) (F' …)`: the two class
      -- arguments are the leading binders themselves (not literals). Detect that so the driver reads its
      -- per-argument classes by specializing to the demand, rather than off fixed literals.
      let structural :=
        bs.size ≥ 2 && args[0]!.isFVar && args[1]!.isFVar && args[0]! == bs[0]! && args[1]! == bs[1]!
      let graded ← if structural then pure ((← inferType bs[0]!).isConstOf ``MapClass) else pure false
      let A := args[2]!; let B := args[3]!
      if graded then
        -- a GRADED relator `∀ (m n) …, Param m n (P …) (P' …)`. Its B-side head (`P'`) is read off the
        -- conclusion too, so the relator ALSO supplies `⟨·⟩` the counterpart `P ↦ P'` (needed for connectives /
        -- `Prop` predicates, which have no separate type former). Homogeneous heads (`List ↦ List`) coincide.
        let some hA := A.getAppFn.constName? | throwError "trocq: graded relator {w} has no head constant"
        return .relator hA B.getAppFn.constName? w
      -- not graded: only a CLOSED base (a fixed-class equivalence of two constant types) is allowed. Every
      -- parameterized relator MUST be graded now — the fixed-class relator pipeline is gone.
      if bs.isEmpty && A.isConst && B.isConst then
        return .base A.constName! B.constName! A B w (← exprToMapClass args[0]!, ← exprToMapClass args[1]!)
      else
        throwError "trocq: relator {w} must be GRADED — take leading `(m n : MapClass)` and conclude `Param m n …`"
    else
      if args.size ≥ 2 then
        let some hA := args[args.size - 2]!.getAppFn.constName?
          | throwError "trocq: term primitive {w} has no A-side head constant"
        return .term hA args[args.size - 1]!.getAppFn w
      else throwError "trocq: cannot classify {w} : {← inferType wit}"

end LeTrocq
