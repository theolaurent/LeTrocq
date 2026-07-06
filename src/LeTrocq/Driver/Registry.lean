/-
The `@[trocq]` REGISTRY: classify a tagged witness, store it, and look it back up for the driver. Three
concerns, one module (they were once `Registry`/`Attr`/`Solver`):

  1. CLASSIFY (`parseEntry` → `RegKind`) — read a tagged constant `w`'s (telescoped) type into one of four
     kinds by the shape of its conclusion:
       • BASE       `w : Param m n A B`      (A,B closed consts, no binders)  — an equivalence of types.
       • RELATOR    `w : ∀ …, Param m n (P …) (P' …)`                        — relates an applied head `P`.
       • TYPEFORMER `w : ∀ params, F args → F' args' → Sort`  (concl a SORT) — the parametricity RELATION of a
                     parameterized type `F` (e.g. `List`/`Option`); its two head constants give `⟨·⟩` the
                     counterpart `F ↦ F'`. Its constructors/recursor register separately as TERM primitives.
       • TERM       `w : ∀ …, R … (c …) (c' …)`  (R a bare relation)        — relates a term head `c ↦ c'`.
  2. STORE (`@[trocq]` attribute + `trocqExt` extension) — tagging runs `parseEntry` eagerly and stores the
     `RegKind`, so a malformed witness is rejected at the tag site.
  3. LOOK UP (`buildAtomPairs`/`buildConsts`/`relatorArgKinds`) — the pure registry reads the driver consumes.
     NOT a grading solver: grading is inline in `Transfer.assemble`; this is only the registry side.
-/
import LeTrocq.Core.Param
import Lean
open Lean Lean.Meta
namespace LeTrocq

/-- install a registered witness in a NESTED map `srcHead ↦ tgtHead ↦ α` (so several registrations for one
    source no longer clobber), recording the PREFERRED (last-registered) target head in `pref` (the synth
    default when no target is demanded). BOTH directions: forward `[hA][hB] := fwd` and `pref[hA] := hB`
    always; the backward `[hB][hA] := bwd`, `pref[hB] := hA` only when `hB` is present and DISTINCT from `hA`
    (a homogeneous head like `List.cons ↦ List.cons` needs no backward entry — its forward witness already
    serves both directions). The backward value is a thunk, run only when inserted. This forward/backward +
    homogeneous-skip policy is what `buildAtomPairs` and `buildCtx` consume. -/
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
    `(a, a', aRel)` — the A-value, the B-value, and their relatedness. Check `xs.size` is a multiple of 3
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

/- ===================== (2) STORE: the `@[trocq]` attribute + environment extension =====================
   Tagging `w` classifies it immediately (via `parseEntry`) and stores the `RegKind`, so a malformed witness
   is rejected at the tag site and the surfaces (`transfer%`/`trocq`/`translate%`) read pre-parsed entries. -/

/-- the classified `@[trocq]` witnesses (bases / relators / term primitives). -/
initialize trocqExt : SimplePersistentEnvExtension RegKind (Array RegKind) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := Array.push
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

initialize registerBuiltinAttribute {
  name  := `trocq
  descr := "register a LeTrocq relatedness witness (base equivalence / relator / term primitive)"
  add   := fun decl _stx _kind => do
    let entry ← (parseEntry decl).run'
    modifyEnv (trocqExt.addEntry · entry)
}

/-- the classified witnesses registered in the given environment. -/
def trocqEntries (env : Environment) : Array RegKind := trocqExt.getState env

/- ===================== (3) LOOK UP: registry reads + relator argument-routing =====================
   The pure lookups the graded translation reads (grading itself is inline in `Transfer.assemble`):
     • `buildAtomPairs`  — type-atom registry from every BASE (both directions via `Param.sym`), pair-indexed
       `srcHead ↦ tgtHead ↦ …` with a preferred (last-registered) target.
     • `buildConsts`     — relator registry from every RELATOR (keyed by the applied head).
     • `relatorArgKinds` — a relator's per-argument routing (`type`/`family`/`term`), read off its type, so the
       `app` rule in `Transfer.assemble` knows how to consume each argument. -/
open MapClass

/- ===================== per-argument kind of a relator ===================== -/
/-- per-argument kind of a relator, read from its (telescoped) type grouped into abstraction-theorem
    triples `(a, a', aRel)` by the SHAPE of the triple's relatedness `aRel`:
      • `.type (m,n)`          — `aRel : Param m n A A'`                  (a TYPE argument);
      • `.family (m,n) domIdx` — `aRel : ∀ a a' (aRel : RA a a'), Param m n (B a)(B' a')` (a dependent type
                                 FAMILY, e.g. `Sigma`/`WTree`'s `β`). `domIdx` is the index of the TYPE
                                 argument that is the family's domain `A` — read off `B`'s own binder type,
                                 so the family need NOT sit right after its domain;
      • `.term`                — `aRel` a bare relation                  (a TERM argument). -/
inductive ArgKind
  | type   (cls : ParamClass)
  | family (cls : ParamClass) (domIdx : Nat)
  | term
  deriving Inhabited

/-- read a relator's per-argument routing off its type (see `ArgKind`). Consumed by `Transfer.assemble`'s
    abstraction-theorem `app` rule: it walks the relator's actual arguments and, per this routing, builds each
    one's `Param` (a TYPE arg / a FAMILY arg) or sends it to the term half (a TERM arg). -/
def relatorArgKinds (wit : Expr) : MetaM (Array ArgKind) := do
  forallTelescopeReducing (← inferType wit) fun bs _ => do
    let triples ← chunkTriples "relator" wit bs
    let mut kinds : Array ArgKind := #[]
    let mut lastTypeIdx : Nat := 0
    for j in [0 : triples.size] do
      let (aBinder, _, aRel) := triples[j]!                 -- `(a, a', aRel)`: the A-binder and the relatedness
      let relTy ← inferType aRel
      if relTy.getAppFn.isConstOf ``Param then
        let a := relTy.getAppArgs
        -- `whnf` the class arguments: for a GRADED relator specialized to a demand they are `variance dem`
        -- projections (e.g. `(listVariance (map1,map0)).1`), which reduce to literal `MapClass`es here.
        kinds := kinds.push (.type (← exprToMapClass (← whnf a[0]!), ← exprToMapClass (← whnf a[1]!)))
        lastTypeIdx := j
      else
        -- a FAMILY arg's relatedness telescopes to a `Param`; anything else is a bare-relation TERM arg.
        let fam? ← forallTelescopeReducing relTy fun _ concl => do
          if concl.getAppFn.isConstOf ``Param then
            let a := concl.getAppArgs
            return some (← exprToMapClass (← whnf a[0]!), ← exprToMapClass (← whnf a[1]!))
          else return none
        match fam? with
        | some cls =>
            -- the family binder `B : A → _` names its domain `A`; find the TYPE-arg triple whose A-binder
            -- IS that `A` (so the right witness is used even if the family is not adjacent to it).
            -- Fall back to the most recent type argument if `A` is not a bare earlier binder.
            let domA := (← whnf (← inferType aBinder)).bindingDomain!
            let mut domIdx := lastTypeIdx
            for k in [0 : j] do
              if triples[k]!.1 == domA then domIdx := k
            kinds := kinds.push (.family cls domIdx)
        | none => kinds := kinds.push .term
    return kinds

/- ===================== registries from the `@[trocq]` extension ===================== -/
/-- type-atom registry from every `@[trocq]` BASE, BOTH directions (the base and its `Param.sym`),
    PAIR-INDEXED `srcHead ↦ tgtHead ↦ (tgtTy, wit, cls)` (so multiple equivalences for one source no
    longer clobber) plus the PREFERRED (last-registered) target per source head — the synth default. A
    diagonal base `A ≃ A` lands at `[A][A]`; its `sym` is skipped as a homogeneous head. -/
def buildAtomPairs : MetaM (NameMap (NameMap (Expr × Expr × ParamClass)) × NameMap Name) := do
  let mut m : NameMap (NameMap (Expr × Expr × ParamClass)) := mkNameMap _
  let mut pref : NameMap Name := mkNameMap _
  for e in trocqEntries (← getEnv) do
    if let .base hA hB tyA tyB witName cls := e then
      let wit ← mkConstWithFreshMVarLevels witName
      let r ← insertBidirPair m pref hA (some hB) (tyB, wit, cls)
        (return (tyA, ← mkAppM ``Param.sym #[wit], (cls.2, cls.1)))
      m := r.1; pref := r.2
  return (m, pref)

/-- constant registry from every `@[trocq]` RELATOR (keyed by the applied head, as written). Includes the
    prelude `Quot` relator (`LeTrocq.Lib.paramQuot`), which registers like any other — not a built-in.
    Every relator is GRADED: its witness opens with `(m n : MapClass)` and the driver specializes it to the
    demand before reading argument classes / applying (the result is already at the demand, no weakening). -/
def buildConsts : MetaM (NameMap Expr) := do
  let mut m := mkNameMap _
  for e in trocqEntries (← getEnv) do
    if let .relator hA _hB witName := e then m := m.insert hA (← mkConstWithFreshMVarLevels witName)
  return m

end LeTrocq
