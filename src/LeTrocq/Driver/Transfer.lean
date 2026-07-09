/-
THE GRADED RELATIONAL TRANSLATION `[·]`: the relatedness witness `[e] : 〚T〛 e ⟨e⟩` (`〚T〛 := [T].R`), on top
of the one term translation `⟨·⟩` (`Counterpart.term`). Two mutually-recursive halves:

  • the TYPE half (`assemble`) — a SINGLE syntax-directed pass driven by a DEMANDED output class. It walks `T`
    top-down and at each former pushes the demand through the `arrowVariance`/`forallVariance` tables to the
    minimal class each part needs, building the node with its graded combinator at exactly that class. A LEAF
    (registered atom or bound type var) reads its available class and WEAKENS to the demand. No constraint
    graph, no fixpoint — infeasibility is just a stuck `assemble` (a `Type` above the `(2a,2a)` ceiling, or a
    leaf that can't weaken).
  • the TERM half (`assembleTerm`) — the abstraction theorem `[t u] = [t] u ⟨u⟩ [u]`, bottoming at registered
    TERM primitives. A PROPOSITION is a `Sort 0` type: `[P] : PLift (P ↔ P')` is the type witness projected by
    `iffOfParam`, so there is no separate `Prop` arm.

BOUND VARIABLES ARE PINNED AT `(4,4)` (the universe combinator's inner class, independent of the capped outer
class); each use weakens down. This is what removes the fixpoint — a var's class is no longer the join of its
uses. `transfer`/`relate` are the type/term entry points.
-/
import LeTrocq.Driver.Registry
import LeTrocq.Driver.Counterpart
import LeTrocq.Combinators
import Lean
open Lean Lean.Meta
namespace LeTrocq.Driver.Transfer
open LeTrocq MapClass

/- ===================== class/weakening helpers ===================== -/
def classToExpr : MapClass → Expr
  | .map0 => mkConst ``MapClass.map0 | .map1 => mkConst ``MapClass.map1
  | .map2a => mkConst ``MapClass.map2a | .map2b => mkConst ``MapClass.map2b
  | .map3 => mkConst ``MapClass.map3 | .map4 => mkConst ``MapClass.map4

/-- proof of `MapClass.le t s = true` (used for weakening and for a combinator's class cap), via `decide`. -/
def leProof (t s : MapClass) : MetaM Expr := do
  mkDecideProof (← mkEq (mkApp2 (mkConst ``MapClass.le) (classToExpr t) (classToExpr s))
                        (mkConst ``Bool.true))

/-- `Param.weaken` applied to coerce a witness `p : Param src.1 src.2 _ _` down to `tgt`. -/
def weakenTo (tgt src : ParamClass) (p : Expr) : MetaM Expr := do
  if tgt == src then return p
  mkAppM ``Param.weaken #[← leProof tgt.1 src.1, ← leProof tgt.2 src.2, p]

/-- the universe combinator for `Type w` at outer class `req`, carrying inner relation class `inner`. The
    level `w` is PINNED explicitly (`mkConst … [w]`) because it is phantom in `paramTypeAt`'s result —
    no argument carries it, so `mkAppM` could only leave it a free mvar (later wrongly zeroed). -/
def mkUniv (w : Level) (req inner : ParamClass) : MetaM Expr := do
  unless MapClass.le req.1 map2a && MapClass.le req.2 map2a do
    throwError "assemble: `Type` at {repr req} exceeds the universe ceiling (2a) — needs univalence"
  let hm ← leProof req.1 map2a
  let hn ← leProof req.2 map2a
  return mkAppN (mkConst ``paramTypeAt [w])
    #[classToExpr req.1, classToExpr req.2, classToExpr inner.1, classToExpr inner.2, hm, hn]

/-- recover `w` from a universe-binder domain `Type w = Sort (w+1)`; a bare `Sort u`/`Prop` domain is out of
    scope for the `Type`-universe path. -/
def typeLevelOf (dom : Expr) : MetaM Level := do
  let .sort l := dom | throwError "assemble: universe-binder domain is not a sort: {dom}"
  match (← instantiateLevelMVars l) with
  | .succ w => return w
  | l       => throwError "assemble: universe binder over `Sort {l}` — only `Type w` domains supported"

/-- the INNER class of every universe combinator: the strength of the `Param p q A A'` a bound type variable is
    offered at. Pinned `(4,4)`: it is the top, independent of the capped outer class, and
    weakens to satisfy every use — which is exactly what lets a bound variable have a fixed class (no fixpoint).
    `paramIdAt (4,4)` is `paramRefl` weakened, so this needs no axiom. -/
def innerClass : ParamClass := (map4, map4)

/-- split a target Π/arrow `B₁ → B₂` / `∀ x', B₂` into `(B₁, rawBody)` (the body keeps its loose bvar 0 for a
    dependent Π). Errors if the target is not a Π-shape — the crisp "shape mismatch" for e.g. `… to (Nat × Nat)`
    against an arrow. -/
def splitForallTgt (B : Expr) : MetaM (Expr × Expr) := do
  match (← whnf B) with
  | .forallE _ d b _ => return (d, b)
  | other => throwError "transfer: target {other} is not a function type (expected a Π/arrow)"

/- ===================== the graded relational translation `[·]` ===================== -/
/-- the shared `[·]` environment, threaded through EVERY arm (both halves): `fvar ↦ (counterpart x',
    witness-or-relatedness)`. For a TYPE binder the third slot is the bound type's `Param` *witness* at inner
    class `(4,4)` (the leaf rule weakens it to each use; a term-primitive consuming the bound type is fed its
    `.R`); for a TERM binder it is the bare relatedness `xRel`. The two never confuse the type/term judgments:
    a type variable's `fvar` has a `Sort` type, a term variable's does not. -/
abbrev SEnv := List (FVarId × Expr × Expr)

/-- registries + the `⟨·⟩` context, threaded through every arm of `[·]` (built once per top-level call). -/
structure Reg where
  atoms    : NameMap (NameMap (Expr × Expr × ParamClass))
  atomPref : NameMap Name
  consts   : NameMap Expr
  ground   : NameMap (Array (Expr × Expr × Expr × ParamClass))
  ctx      : LeTrocq.Counterpart.Ctx

/-- does `e` bind over a `Sort` (a `∀`/`λ` whose domain is a universe)? Such a type/term is EXCLUDED from the
    whole-diagonal short-circuit: a universe quantifier must keep its parametric witness (the free theorem),
    not collapse to the discrete equality relation `paramRefl` carries. -/
def containsSortBinder (e : Expr) : Bool :=
  (e.find? fun s => match s with
    | .forallE _ d _ _ => d.isSort
    | .lam _ d _ _     => d.isSort
    | _ => false).isSome

/-- GROUND leaf: a registered closed-type equivalence (`List Unit ≃ Nat`), matched WHOLE. Scan the ground
    entries filed under `A`'s head, keeping the LAST whose source type is `isDefEq A` and whose target is
    `isDefEq B`, then weaken its witness to the demand. `none` when no ground base is registered under the head
    or matches, so the caller falls through to the ordinary rules. -/
def tryGround (reg : Reg) (A B : Expr) (dem : ParamClass) : MetaM (Option Expr) := do
  let some h := A.getAppFn.constName? | return none
  let some cands := NameMap.find? reg.ground h | return none
  let mut found : Option (Expr × ParamClass) := none
  for (srcTy, tgtTy, wit, cls) in cands do
    if (← diagEq? A srcTy) && (← diagEq? B tgtTy) then found := some (wit, cls)
  match found with
  | some (wit, cls) => return some (← weakenTo dem cls wit)
  | none            => return none

mutual
/-- `[·]` on a TYPE — the syntax-directed, DEMAND-driven half: given BOTH ends `A` (source) and `B` (target)
    and a demanded class `dem`, build the witness `Param dem A B` DIRECTLY, pushing the demand through
    `arrowVariance`/`forallVariance` to the minimal class each part needs. Both ends are walked in LOCKSTEP — at
    every former `B` is destructured in parallel with `A`, so each sub-part's counterpart is READ off `B` (never
    synthesised here; the surfaces precompute `B = ⟨A⟩` via `Counterpart.term`). ONE environment `senv`
    (`fvar ↦ (counterpart, witness/relatedness)`) threads every in-scope binder, type and term alike. A relator's
    TERM arguments go to `assembleTerm` (`[t u] = [t] u ⟨u⟩ [u]`). Registered atoms and bound type variables are
    leaves: they read their available class and weaken to `dem`. -/
partial def assemble (reg : Reg) (senv : SEnv) (A B : Expr) (dem : ParamClass) : MetaM Expr := do
  -- GROUND base: a registered closed-type equivalence (e.g. `List Unit ≃ Nat`) matched WHOLE. It BEATS both the
  -- structural relator descent below AND the diagonal short-circuit (which would otherwise collapse `List Unit`
  -- to itself, since `⟨List Unit⟩ = List Unit`), so it must be tried first.
  if let some out ← tryGround reg A B dem then return out
  -- WHOLE-DIAGONAL short-circuit: a type that transfers to ITSELF (`A` defeq `B`) is built as the generic
  -- `paramRefl` (relation `PLift (a=b)`, map `id`), weakened to the demand — no structural descent, no per-type
  -- registration. Skipped for a bare sort / a universe binder (those keep their parametric witness).
  if !A.isSort && !containsSortBinder A then
    if ← diagEq? A B then
      return ← weakenTo dem (map4, map4) (← mkAppM ``paramRefl #[A])
  match A, B with
  | .const name _, _ =>
      -- LEAF: a registered base atom, available at its registered class `regC`; weaken to the demand. The base
      -- is selected by the TARGET head `B` — both ends known, so no preferred-target default is consulted.
      let some tgtMap := reg.atoms.find? name | throwError "assemble: atom {name} not registered"
      let some tgtHead := (← whnf B).getAppFn.constName?
        | throwError "assemble: target type {B} has no head constant"
      let some (_, wit, regC) := tgtMap.find? tgtHead
        | throwError "assemble: no registered base {name} ≃ {tgtHead}"
      weakenTo dem regC wit
  | .fvar id, _ =>
      -- LEAF: a bound TYPE variable, offered at inner class `(4,4)`; weaken its witness to the demand.
      let some (_, _, aRel) := senv.find? (·.1 == id)
        | throwError "assemble: unbound type variable {A}"
      weakenTo dem innerClass aRel
  | .sort lvl, _ =>
      -- `Prop` (Sort 0) reaches the full `(4,4)` via `paramProp` (completeness = `propext`, coherence free by
      -- proof irrelevance); `Type w` (Sort (w+1)) uses the level-`w` universe combinator at `dem`, capped at the
      -- `(2a,2a)` no-univalence ceiling (`mkUniv`), carrying the bound variable at inner class `(4,4)`.
      match (← instantiateLevelMVars lvl) with
      | .zero   => mkAppM ``paramPropAt #[classToExpr dem.1, classToExpr dem.2]
      | .succ w => mkUniv w dem innerClass
      | l       => throwError "assemble: unsupported sort `Sort {l}` (only `Prop` / `Type w`)"
  | .forallE n A₁ A₂ _, _ => do
      -- destructure the TARGET Π/arrow in lockstep: `B₁` for the domain, `B₂` (raw, loose bvar) for the codomain.
      let (B₁, B₂) ← splitForallTgt B
      if A₂.hasLooseBVar 0 then
        match A₁ with
        | .sort _ => do
            -- `∀ A : Type, A₂` (type-domain Π). Domain via the universe combinator at `forallVariance(dem).1`,
            -- inner `(4,4)`; codomain family under the binder at `forallVariance(dem).2`, with `A` recorded in
            -- `senv` as a `(4,4)` type var, its counterpart the fresh `a'` (the target binder).
            let (domDem, codDem) := forallVariance dem
            let w ← typeLevelOf A₁
            let domWit ← mkUniv w domDem innerClass
            let pb ← withLocalDeclD n A₁ fun a =>
              withLocalDeclD (n.appendAfter "'") A₁ fun a' => do
                let raaTy ← mkAppM ``Param.R #[domWit, a, a']
                withLocalDeclD (n.appendAfter "R") raaTy fun aRel => do
                  mkLambdaFVars #[a, a', aRel]
                    (← assemble reg ((a.fvarId!, a', aRel) :: senv)
                        (A₂.instantiate1 a) (B₂.instantiate1 a') codDem)
            mkAppM ``paramForall #[classToExpr dem.1, classToExpr dem.2, domWit, pb]
        | _ => do
            -- `∀ x : T, A₂` (term-domain Π over ANY buildable domain). Build the domain witness at
            -- `forallVariance(dem).1`, read the two sides off its `Param` type, and check the body at
            -- `forallVariance(dem).2` with `x` a TERM variable whose relatedness is `domWit.R x x'`.
            let (domDem, codDem) := forallVariance dem
            let domWit ← assemble reg senv A₁ B₁ domDem
            let domTy := (← whnf (← instantiateMVars (← inferType domWit))).getAppArgs
            let pb ← withLocalDeclD n domTy[2]! fun x =>
              withLocalDeclD (n.appendAfter "'") domTy[3]! fun x' => do
                let xRTy ← mkAppM ``Param.R #[domWit, x, x']
                withLocalDeclD (n.appendAfter "R") xRTy fun xRel => do
                  mkLambdaFVars #[x, x', xRel]
                    (← assemble reg ((x.fvarId!, x', xRel) :: senv)
                        (A₂.instantiate1 x) (B₂.instantiate1 x') codDem)
            mkAppM ``paramForall #[classToExpr dem.1, classToExpr dem.2, domWit, pb]
      else
        -- `A₁ → A₂` (non-dependent arrow). Parts at `arrowVariance(dem)`.
        let (domDem, codDem) := arrowVariance dem
        mkAppM ``paramArrow
          #[classToExpr dem.1, classToExpr dem.2,
            ← assemble reg senv A₁ B₁ domDem,
            ← assemble reg senv (A₂.instantiate1 (mkConst ``True)) (B₂.instantiate1 (mkConst ``True)) codDem]
  | .app .., _ => do
      -- the abstraction theorem `[head a₁ … aₙ] = [head] a₁ b₁ [a₁] … aₙ bₙ [aₙ]`. Routing (type/family/term)
      -- from the relator's `relatorArgKinds`; each argument's counterpart `bᵢ` is READ off the target `B`
      -- (`F' b₁ … bₙ`), never synthesised. A TYPE arg's `Param` is assembled at the relator's declared class; a
      -- FAMILY arg's is the `Param` family (its B-side is `bᵢ` directly); a TERM arg's relatedness is `[aᵢ]`.
      let some head := A.getAppFn.constName? | throwError "assemble: application head {A.getAppFn} is not a constant"
      let some relator0 := reg.consts.find? head | throwError "assemble: constant {head} not registered"
      -- every relator is GRADED: specialize it to the demanded output class FIRST; its residual argument
      -- classes are then `variance dem` (read below by `relatorArgKinds`), and the result is already at `dem`.
      let relator := mkAppN relator0 #[classToExpr dem.1, classToExpr dem.2]
      let kinds ← relatorArgKinds relator
      let args := A.getAppArgs
      unless args.size == kinds.size do
        throwError "assemble: relator {head} takes {kinds.size} arguments but is applied to {args.size}"
      -- the target `F' b₁ …` supplies each argument's counterpart `bᵢ` (positionally aligned with `args`). NO
      -- `whnf` — it would unfold a reducible former/predicate (`Pos'`) and break the alignment with `args`.
      let tgtArgs := (← instantiateMVars B).getAppArgs
      unless tgtArgs.size == args.size do
        throwError "assemble: target {B} of {head} has {tgtArgs.size} arguments but expected {args.size}"
      let mut argExprs : Array Expr := #[]
      let mut argWits : Array (Option Expr) := Array.replicate args.size none  -- each TYPE arg's witness, by index
      for i in [0 : args.size] do
        let arg := args[i]!
        let argTgt := tgtArgs[i]!
        match kinds[i]! with
        | .type cls => do                                  -- TYPE arg: build its `Param` at the relator's class
            let tR ← assemble reg senv arg argTgt cls
            argExprs := argExprs ++ #[arg, argTgt, tR]
            argWits := argWits.set! i (some tR)
        | .family cls domIdx => do                         -- FAMILY arg: build the `Param` family; B-side is `argTgt`
            let some paWit := argWits[domIdx]!
              | throwError "assemble: family argument {i} of {head} has no domain type argument (#{domIdx})"
            let paTy := (← whnf (← instantiateMVars (← inferType paWit))).getAppArgs
            let pbWit ← withLocalDeclD `a paTy[2]! fun a => withLocalDeclD `a' paTy[3]! fun a' => do
              let aRTy ← mkAppM ``Param.R #[paWit, a, a']
              withLocalDeclD `aRel aRTy fun aRel => do
                mkLambdaFVars #[a, a', aRel]
                  (← assemble reg ((a.fvarId!, a', aRel) :: senv) (arg.beta #[a]) (argTgt.beta #[a']) cls)
            argExprs := argExprs ++ #[arg, argTgt, pbWit]
        | .term => do                                      -- TERM arg: counterpart `bᵢ` (off `B`) + relatedness `[aᵢ]`
            let aRel ← assembleTerm reg senv arg argTgt
            argExprs := argExprs ++ #[arg, argTgt, aRel]
      -- applied positionally (`mkAppN` fills implicit binders too, e.g. a predicate's `{A A'}`); the relators
      -- are monomorphic so no universe grounding is needed. Already at `dem`, so no final weakening.
      return mkAppN relator argExprs
  | _, _ => throwError "assemble: unsupported type pair {A} / {B}"

/-- `[·]` on a TYPE embedded in a term: its `Param` witness (both ends `A`/`B` known), at the trivial class
    `(0,0)` — a term position consumes only the relation `.R`, which is grade-invariant, so the cheapest class
    suffices. The ambient `senv` is threaded in so a DEPENDENT type resolves — e.g. `Boxed b` / `Vec n` with
    `b`/`n` bound by an outer λ (the bound term supplies its relatedness), or a type over an outer λ-bound TYPE
    variable (its `(4,4)` witness sits in `senv`, and `assemble`'s leaf rule weakens it). -/
partial def assembleType (reg : Reg) (senv : SEnv) (A B : Expr) : MetaM Expr :=
  assemble reg senv A B (map0, map0)

/-- `〚·〛 := [·].R` (`〚A〛 := [A].R`): the RELATION of a type, projected off the graded witness `[·]`
    (`assembleType`) builds for the pair `A`/`B`. All a TERM position ever consumes of a type, and
    grade-invariant — so `assembleType`'s cheapest `(0,0)` witness suffices. -/
partial def assembleRel (reg : Reg) (senv : SEnv) (A B : Expr) : MetaM Expr := do
  mkAppM ``Param.R #[← assembleType reg senv A B]

/-- `[·]` on a TERM (the abstraction theorem): its relatedness `[e] : 〚T〛 e e'`, given BOTH the term `e` and
    its counterpart `e'` (precomputed by the caller via `Counterpart.term`; every sub-counterpart is READ off
    `e'` in lockstep, never synthesised). A TYPE-valued sub-term contributes its relation `(assembleType …).R`.
    A PROPOSITION `P` is just a `Sort 0` type: its relatedness `[P] : 〚Prop〛 P P' = PLift (P ↔ P')` is the
    `(1,1)` `Param` witness the relator path builds, projected via `iffOfParam` — no separate `Prop` arm.
    Bottoms out at registered TERM primitives (`ctx.terms`). -/
partial def assembleTerm (reg : Reg) (senv : SEnv) (e e' : Expr) : MetaM Expr := do
  let ty ← inferType e
  if let .sort lvl := ty then
    if (← instantiateLevelMVars lvl) == levelZero then
      -- a PROPOSITION: build its `(1,1)` `Param` witness through the ordinary relator/type path, then project
      -- to `PLift (P ↔ P')`. A bound `Prop` variable's relatedness already sits in `senv` as that `PLift`.
      match e with
      | .fvar id =>
          match senv.find? (·.1 == id) with
          | some (_, _, w) => return w
          | none => throwError "assemble: unbound proposition variable {e}"
      | _ =>
          let w ← assemble reg senv e e' (map1, map1)
          return ← mkAppM ``PLift.up #[← mkAppM ``iffOfParam #[w]]
    else return ← assembleRel reg senv e e'
  -- GROUND TERM: `e` matches a registered partial-application pattern (`@List.cons Unit ()`) WHOLE ⇒ its
  -- relatedness is the stored witness; the `.app` spine below feeds it the remaining `(arg, bᵢ, [arg])`
  -- triple. Before the diagonal so a ground term never collapses to `PLift.up rfl`.
  if let some h := e.getAppFn.constName? then
    if let some cands := NameMap.find? reg.ctx.groundTerms h then
      for (patSrc, _tgt, wit) in cands do
        if e.getAppNumArgs == patSrc.getAppNumArgs && (← diagEq? e patSrc) then
          return wit
  -- WHOLE-DIAGONAL short-circuit: a term that transfers to ITSELF has relatedness `PLift.up rfl` (`[e] : 〚T〛 e e`
  -- with `〚T〛 = PLift (a=b)`, from the diagonal `assemble` of its type). Gated on BOTH the TYPE transferring
  -- diagonally (`ty` defeq `ty' := typeof e'`) AND the term being its own counterpart (`e` defeq `e'`) — the
  -- latter rejects a term over a TRANSFERRED bound variable whose type is nonetheless diagonal. Also exclude a
  -- term whose TYPE is polymorphic (a bare constructor `@List.cons : ∀{α}, …`): its diagonal relatedness is a
  -- FUNCTION, not `PLift.up rfl`, and collapsing it would break the application spine.
  if !containsSortBinder e && !containsSortBinder ty then
    if (← diagEq? ty (← inferType e')) && (← diagEq? e e') then
      return ← mkAppM ``PLift.up #[← mkEqRefl e]
  if let some n := LeTrocq.Counterpart.natNumeral? e then
    if (← whnf ty).isConstOf ``Nat then return ← assembleTerm reg senv (LeTrocq.Counterpart.natExpr n) e'
  match e with
  | .fvar id =>
      match senv.find? (·.1 == id) with
      | some (_, _, xRel) => return xRel
      | none => throwError "assemble: unbound variable {e}"
  | .const c _ =>
      -- select the primitive's relatedness by the RESULT-TYPE head of the counterpart `e'` (the key `ctx.terms`
      -- is filed under) — both ends known, so no preferred default is consulted.
      let key ← LeTrocq.Counterpart.resultTypeHead e'
      match reg.ctx.terms.find? c with
      | some tgtMap =>
          let some (_, wit) := tgtMap.find? key
            | throwError "assemble: no relatedness for term {c} at target {key}"
          return wit
      | none => throwError "assemble: unregistered constant {c}"
  | .app .. => do
      -- SPINE, one argument at a time (`[f a] = [f] a a' [a]`): peel `e` and its counterpart `e'` in lockstep.
      -- A ground-term head (an appFn subterm) is caught by the ground rule above on the recursive `[f]` call.
      let fR ← assembleTerm reg senv e.appFn! e'.appFn!
      let aRel ← assembleTerm reg senv e.appArg! e'.appArg!
      return mkApp3 fR e.appArg! e'.appArg! aRel
  | .lam n A b _ => do
      -- the counterpart `e'` is `fun x' : A' => b'`; read `A'`/`b'` off it in lockstep.
      let A' := e'.bindingDomain!
      -- the bound variable's relatedness is `〚A〛 = [A].R`: for a type binder the parametricity relation, for
      -- a term/base binder the bare relatedness. (`assembleRel` projects it off the graded witness `[A]`.)
      let relA ← assembleRel reg senv A A'
      withLocalDeclD n A fun x =>
      withLocalDeclD (n.appendAfter "'") A' fun x' =>
      withLocalDeclD (n.appendAfter "R") (mkApp2 relA x x') fun xRel => do
        mkLambdaFVars #[x, x', xRel]
          (← assembleTerm reg ((x.fvarId!, x', xRel) :: senv) (b.instantiate1 x) (e'.bindingBody!.instantiate1 x'))
  | e => throwError "assemble: unsupported term {e}"
end

/-- the registries + `⟨·⟩` context, built once from the `@[trocq]` environment extension. -/
def mkReg : MetaM Reg := do
  let (atoms, atomPref) ← buildAtomPairs
  return { atoms, atomPref, consts := ← buildConsts, ground := ← buildGround,
           ctx := ← LeTrocq.Counterpart.buildCtx }

/-- default any genuinely-free residual universe mvars (e.g. the universe combinator's relation level, or a
    universe-poly registered witness's level) to 0 — they are unconstrained, so any level is sound. -/
def defaultFreeLevels (wit : Expr) : MetaM Expr := do
  let wit ← instantiateMVars wit
  let st := Lean.collectLevelMVars (Lean.collectLevelMVars {} wit) (← instantiateMVars (← inferType wit))
  for mid in st.result do
    unless (← isLevelMVarAssigned mid) do assignLevelMVar mid levelZero
  instantiateMVars wit

/-- the B-side counterpart `⟨e⟩` of a type/term, via `Counterpart.term` over the built registries. The surfaces
    call this to obtain the missing end BEFORE `assemble`/`assembleTerm` (which are pure two-ended passes). -/
def counterpart (e : Expr) : MetaM Expr := do
  let c ← LeTrocq.Counterpart.term (← LeTrocq.Counterpart.buildCtx) [] e none
  -- `Counterpart.term` builds the counterpart raw (no type-checking), so a type former's universe mvar is left
  -- unconstrained (e.g. `Eq.{?u}` / `List.{?u}`). Type-check to unify each from its actual arguments (`Eq.{1}`
  -- over `Nat`), THEN zero any genuinely-unconstrained residual level — blindly zeroing first would wrongly pin
  -- `Eq.{0}` (a `Prop` equality) over a `Type` argument.
  Lean.Meta.check c
  defaultFreeLevels c

/-- `[A ≃ B]@root` for a TYPE PAIR: assemble the witness `Param root A B` DIRECTLY in one two-ended pass —
    every node built by the graded combinator at the minimal class the demand pushes down, both ends walked in
    lockstep. Drives `transfer from/to`/`trocq`; the caller precomputes whichever end it does not name. (Named
    `transferType`, not `transfer`, so it never collides with the `transfer` surface keyword.) -/
partial def transferType (A B : Expr) (root : ParamClass) : MetaM Expr := do
  defaultFreeLevels (← assemble (← mkReg) [] A B root)

/-- `[t]` for a TERM: its relatedness by the abstraction theorem, against the precomputed counterpart `⟨t⟩`.
    Drives `relate`. (Named `relateTerm`, not `relate`, so it never collides with the `relate` surface keyword.) -/
partial def relateTerm (e : Expr) : MetaM Expr := do
  let reg ← mkReg
  let e' ← instantiateMVars (← LeTrocq.Counterpart.term reg.ctx [] e none)
  defaultFreeLevels (← assembleTerm reg [] e e')

end LeTrocq.Driver.Transfer
