/-
THE GRADED RELATIONAL TRANSLATION `[·]`: the relatedness witness `[e] : 〚T〛 e ⟨e⟩` (`〚T〛 := [T].R`), on top
of the term translation `⟨·⟩` (`Counterpart.term`). Two mutually-recursive halves:
  • TYPE (`assemble`) — a single syntax-directed pass driven by a DEMANDED output class: at each former, push
    the demand through `arrowVariance`/`forallVariance` to the minimal class each part needs; a LEAF reads its
    available class and weakens to the demand. No constraint graph, no fixpoint — infeasibility is just a stuck
    pass. Bound variables are PINNED at `(4,4)` (each use weakens down), which is what removes the fixpoint.
  • TERM (`assembleTerm`) — the abstraction theorem `[t u] = [t] u ⟨u⟩ [u]`, bottoming at registered TERM
    primitives. A PROPOSITION is a `Sort 0` type; `[P] : PLift (P ↔ P')` via `iffOfParam`, no separate arm.
`transferType`/`relateTerm` are the type/term entry points.
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

/-- the universe combinator for `Type w` at outer class `req`, inner class `inner`. Level `w` is PINNED
    explicitly because it is phantom in `paramTypeAt`'s result — `mkAppM` would leave it a free mvar. -/
def mkUniv (w : Level) (req inner : ParamClass) : MetaM Expr := do
  unless MapClass.le req.1 map2a && MapClass.le req.2 map2a do
    throwError "assemble: `Type` at {repr req} exceeds the universe ceiling (2a) — needs univalence"
  let hm ← leProof req.1 map2a
  let hn ← leProof req.2 map2a
  return mkAppN (mkConst ``paramTypeAt [w])
    #[classToExpr req.1, classToExpr req.2, classToExpr inner.1, classToExpr inner.2, hm, hn]

/-- recover `w` from a universe-binder domain `Type w = Sort (w+1)`; a bare `Sort u`/`Prop` is out of scope. -/
def typeLevelOf (dom : Expr) : MetaM Level := do
  let .sort l := dom | throwError "assemble: universe-binder domain is not a sort: {dom}"
  match (← instantiateLevelMVars l) with
  | .succ w => return w
  | l       => throwError "assemble: universe binder over `Sort {l}` — only `Type w` domains supported"

/-- the INNER class every universe combinator offers a bound type variable at. Pinned `(4,4)` (the top): it
    weakens to satisfy every use, giving each bound variable a fixed class (no fixpoint), and needs no axiom. -/
def innerClass : ParamClass := (map4, map4)

/-- split a target Π/arrow into `(B₁, rawBody)` (body keeps its loose bvar 0 for a dependent Π); errors on a
    non-Π target — the crisp shape mismatch. -/
def splitForallTgt (B : Expr) : MetaM (Expr × Expr) := do
  match (← whnf B) with
  | .forallE _ d b _ => return (d, b)
  | other => throwError "transfer: target {other} is not a function type (expected a Π/arrow)"

/- ===================== the graded relational translation `[·]` ===================== -/
/-- the shared `[·]` environment, threaded through every arm: `fvar ↦ (counterpart x', witness-or-relatedness)`.
    A TYPE binder's third slot is the bound type's `Param` witness at inner class `(4,4)` (the leaf rule weakens
    it); a TERM binder's is the bare relatedness `xRel`. Distinguished by the `fvar` type (a type var's is a
    `Sort`). -/
abbrev SEnv := List (FVarId × Expr × Expr)

/-- registries + the `⟨·⟩` context, threaded through every arm of `[·]` (built once per top-level call). -/
structure Reg where
  atoms    : NameMap (NameMap (Expr × Expr × ParamClass))
  atomPref : NameMap Name
  consts   : NameMap Expr
  ground   : NameMap (Array (Expr × Expr × Expr × ParamClass))
  ctx      : LeTrocq.Counterpart.Ctx

/-- does `e` bind over a `Sort`? Such a type/term is EXCLUDED from the whole-diagonal short-circuit: a universe
    quantifier must keep its parametric witness (the free theorem), not collapse to `paramRefl`'s equality. -/
def containsSortBinder (e : Expr) : Bool :=
  (e.find? fun s => match s with
    | .forallE _ d _ _ => d.isSort
    | .lam _ d _ _     => d.isSort
    | _ => false).isSome

/-- GROUND leaf: a registered closed-type equivalence (`List Unit ≃ Nat`) matched WHOLE. Scan entries under
    `A`'s head, keep the LAST with source defeq `A` and target defeq `B`, weaken to the demand; `none` (fall
    through to the ordinary rules) if none matches. -/
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
/-- `[·]` on a TYPE — the DEMAND-driven half: given both ends `A`/`B` and demanded class `dem`, build
    `Param dem A B` directly, pushing the demand through `arrowVariance`/`forallVariance` to the minimal class
    each part needs. Both ends walk in LOCKSTEP, so each sub-part's counterpart is read off `B`, never
    synthesised (surfaces precompute `B = ⟨A⟩`). Atoms and bound type variables are leaves that weaken to `dem`;
    relator TERM arguments go to `assembleTerm`. -/
partial def assemble (reg : Reg) (senv : SEnv) (A B : Expr) (dem : ParamClass) : MetaM Expr := do
  -- GROUND base matched WHOLE. Tried FIRST: it must beat both the structural descent and the diagonal
  -- short-circuit (which would otherwise collapse `List Unit` to itself, since `⟨List Unit⟩ = List Unit`).
  if let some out ← tryGround reg A B dem then return out
  -- WHOLE-DIAGONAL short-circuit: a type transferring to ITSELF (`A` defeq `B`) is `paramRefl` weakened to the
  -- demand — no descent. Skipped for a sort / universe binder (those keep their parametric witness).
  if !A.isSort && !containsSortBinder A then
    if ← diagEq? A B then
      return ← weakenTo dem (map4, map4) (← mkAppM ``paramRefl #[A])
  match A, B with
  | .const name _, _ =>
      -- LEAF: a registered base atom at class `regC`, weakened to the demand; the base is selected by the
      -- TARGET head `B` (both ends known, so no preferred-target default).
      let some tgtMap := reg.atoms.find? name | throwError "assemble: atom {name} not registered"
      let some tgtHead := (← whnf B).getAppFn.constName?
        | throwError "assemble: target type {B} has no head constant"
      let some (_, wit, regC) := tgtMap.find? tgtHead
        | throwError "assemble: no registered base {name} ≃ {tgtHead}"
      weakenTo dem regC wit
  | .fvar id, _ =>
      -- LEAF: a bound TYPE variable at inner class `(4,4)`, weakened to the demand.
      let some (_, _, aRel) := senv.find? (·.1 == id)
        | throwError "assemble: unbound type variable {A}"
      weakenTo dem innerClass aRel
  | .sort lvl, _ =>
      -- `Prop` (Sort 0) reaches `(4,4)` via `paramProp`; `Type w` uses the universe combinator at `dem`, capped
      -- at the `(2a,2a)` no-univalence ceiling (`mkUniv`), inner class `(4,4)`.
      match (← instantiateLevelMVars lvl) with
      | .zero   => mkAppM ``paramPropAt #[classToExpr dem.1, classToExpr dem.2]
      | .succ w => mkUniv w dem innerClass
      | l       => throwError "assemble: unsupported sort `Sort {l}` (only `Prop` / `Type w`)"
  | .forallE n A₁ A₂ _, _ => do
      -- destructure the TARGET Π/arrow in lockstep: `B₁` domain, `B₂` (raw) codomain.
      let (B₁, B₂) ← splitForallTgt B
      if A₂.hasLooseBVar 0 then
        match A₁ with
        | .sort _ => do
            -- `∀ A : Type, A₂` (type-domain Π): domain via the universe combinator, codomain family under the
            -- binder with `A` recorded in `senv` as a `(4,4)` type var, counterpart the fresh `a'`.
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
            -- `∀ x : T, A₂` (term-domain Π): build the domain witness, read its two sides off the `Param` type,
            -- check the body with `x` a TERM variable whose relatedness is `domWit.R x x'`.
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
      -- the abstraction theorem `[head a₁ … aₙ] = [head] a₁ b₁ [a₁] …`. Routing (type/family/term) from the
      -- relator's `relatorArgKinds`; each counterpart `bᵢ` is read off the target `B`, never synthesised.
      let some head := A.getAppFn.constName? | throwError "assemble: application head {A.getAppFn} is not a constant"
      let some relator0 := reg.consts.find? head | throwError "assemble: constant {head} not registered"
      -- GRADED relator: specialize to the demanded output class FIRST, so its residual argument classes are
      -- `variance dem` and the result is already at `dem`.
      let relator := mkAppN relator0 #[classToExpr dem.1, classToExpr dem.2]
      let kinds ← relatorArgKinds relator
      let args := A.getAppArgs
      unless args.size == kinds.size do
        throwError "assemble: relator {head} takes {kinds.size} arguments but is applied to {args.size}"
      -- the target `F' b₁ …` supplies each counterpart `bᵢ`, positionally aligned with `args`. NO `whnf`: it
      -- would unfold a reducible former/predicate and break the alignment.
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
      -- applied positionally (`mkAppN` fills implicit binders too); relators are monomorphic and already at
      -- `dem`, so no universe grounding and no final weakening.
      return mkAppN relator argExprs
  | _, _ => throwError "assemble: unsupported type pair {A} / {B}"

/-- `[·]` on a TYPE embedded in a term: its `Param` witness at the trivial class `(0,0)` — a term consumes only
    `.R`, which is grade-invariant, so the cheapest class suffices. `senv` is threaded so a DEPENDENT type
    (`Vec n`, or a type over a λ-bound type variable) resolves. -/
partial def assembleType (reg : Reg) (senv : SEnv) (A B : Expr) : MetaM Expr :=
  assemble reg senv A B (map0, map0)

/-- `〚·〛 := [·].R`: the RELATION of a type, projected off the `(0,0)` witness `assembleType` builds. -/
partial def assembleRel (reg : Reg) (senv : SEnv) (A B : Expr) : MetaM Expr := do
  mkAppM ``Param.R #[← assembleType reg senv A B]

/-- `[·]` on a TERM (the abstraction theorem): its relatedness `[e] : 〚T〛 e e'`, given both `e` and its
    counterpart `e'` (every sub-counterpart read off `e'` in lockstep, never synthesised). A TYPE-valued sub-term
    contributes `.R`; a PROPOSITION `P` is a `Sort 0` type, its `[P] : PLift (P ↔ P')` via `iffOfParam`. Bottoms
    out at registered TERM primitives (`ctx.terms`). -/
partial def assembleTerm (reg : Reg) (senv : SEnv) (e e' : Expr) : MetaM Expr := do
  let ty ← inferType e
  if let .sort lvl := ty then
    if (← instantiateLevelMVars lvl) == levelZero then
      -- a PROPOSITION: build its `(1,1)` witness through the ordinary path, project to `PLift (P ↔ P')`. A bound
      -- `Prop` variable's relatedness already sits in `senv` as that `PLift`.
      match e with
      | .fvar id =>
          match senv.find? (·.1 == id) with
          | some (_, _, w) => return w
          | none => throwError "assemble: unbound proposition variable {e}"
      | _ =>
          let w ← assemble reg senv e e' (map1, map1)
          return ← mkAppM ``PLift.up #[← mkAppM ``iffOfParam #[w]]
    else return ← assembleRel reg senv e e'
  -- GROUND TERM: `e` matches a registered partial-application pattern WHOLE ⇒ its relatedness is the stored
  -- witness (the `.app` spine feeds the remaining args). Before the diagonal so it never collapses to `rfl`.
  if let some h := e.getAppFn.constName? then
    if let some cands := NameMap.find? reg.ctx.groundTerms h then
      for (patSrc, _tgt, wit) in cands do
        if e.getAppNumArgs == patSrc.getAppNumArgs && (← diagEq? e patSrc) then
          return wit
  -- WHOLE-DIAGONAL short-circuit: a term transferring to ITSELF has relatedness `PLift.up rfl`. SOUNDNESS gating:
  -- both the TYPE diagonal (`ty` defeq typeof `e'`) AND the term being its own counterpart (`e` defeq `e'`) —
  -- the latter rejects a term over a TRANSFERRED bound variable whose type is nonetheless diagonal. Also exclude
  -- a polymorphic type (bare constructor), whose diagonal relatedness is a FUNCTION, not `rfl`.
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
      -- select the primitive's relatedness by the RESULT-TYPE head of `e'` (the key `ctx.terms` is filed under).
      let key ← LeTrocq.Counterpart.resultTypeHead e'
      match reg.ctx.terms.find? c with
      | some tgtMap =>
          let some (_, wit) := tgtMap.find? key
            | throwError "assemble: no relatedness for term {c} at target {key}"
          return wit
      | none => throwError "assemble: unregistered constant {c}"
  | .app .. => do
      -- SPINE `[f a] = [f] a a' [a]`: peel `e`/`e'` in lockstep (a ground-term head is caught on the `[f]` call).
      let fR ← assembleTerm reg senv e.appFn! e'.appFn!
      let aRel ← assembleTerm reg senv e.appArg! e'.appArg!
      return mkApp3 fR e.appArg! e'.appArg! aRel
  | .lam n A b _ => do
      -- counterpart `e'` is `fun x' : A' => b'`; read `A'`/`b'` off it in lockstep.
      let A' := e'.bindingDomain!
      -- the bound variable's relatedness is `〚A〛 = [A].R` (`assembleRel` projects it off `[A]`).
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

/-- default any genuinely-free residual universe mvars to 0 — unconstrained, so any level is sound. -/
def defaultFreeLevels (wit : Expr) : MetaM Expr := do
  let wit ← instantiateMVars wit
  let st := Lean.collectLevelMVars (Lean.collectLevelMVars {} wit) (← instantiateMVars (← inferType wit))
  for mid in st.result do
    unless (← isLevelMVarAssigned mid) do assignLevelMVar mid levelZero
  instantiateMVars wit

/-- the B-side counterpart `⟨e⟩`, via `Counterpart.term`. The surfaces call this for the missing end before the
    two-ended `assemble`/`assembleTerm`. -/
def counterpart (e : Expr) : MetaM Expr := do
  let c ← LeTrocq.Counterpart.term (← LeTrocq.Counterpart.buildCtx) [] e none
  -- `Counterpart.term` builds raw, leaving type-former universe mvars unconstrained (`Eq.{?u}`). Type-check to
  -- unify each from its arguments, THEN zero the residuals — zeroing first would wrongly pin `Eq.{0}` (a `Prop`
  -- equality) over a `Type` argument.
  Lean.Meta.check c
  defaultFreeLevels c

/-- `Param root A B` for a TYPE PAIR, assembled directly in one two-ended pass. Drives `transfer from/to`/`trocq`
    (the caller precomputes whichever end it does not name). Named `transferType` to avoid the surface keyword. -/
partial def transferType (A B : Expr) (root : ParamClass) : MetaM Expr := do
  defaultFreeLevels (← assemble (← mkReg) [] A B root)

/-- `[t]` for a TERM: its relatedness against the counterpart `⟨t⟩`. Drives `relate`. Named `relateTerm` to
    avoid the surface keyword. -/
partial def relateTerm (e : Expr) : MetaM Expr := do
  let reg ← mkReg
  let e' ← instantiateMVars (← LeTrocq.Counterpart.term reg.ctx [] e none)
  defaultFreeLevels (← assembleTerm reg [] e e')

end LeTrocq.Driver.Transfer
