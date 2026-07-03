/-
THE GRADED RELATIONAL TRANSLATION `[·]` (DESIGN.md's `[·]`): produce the relatedness witness
`[e] : 〚T〛 e ⟨e⟩` (with `〚T〛 := [T].R`), relying on the one term translation `⟨·⟩` (`LeTrocq.Translate.term`).

It has two mutually-recursive halves — as DESIGN.md itself splits `[Πx:A.B]` from `[t u]`:

  • the TYPE half (`assemble`) is a SINGLE syntax-directed pass driven by a DEMANDED output class (bidir_solver.md):
    `assemble : Expr → ParamClass → MetaM Expr`. It walks the type `Expr` top-down, and at each structural former
    pushes the demand THROUGH the `depArrow`/`depPi`/`depType` tables (`Lattice`) to the minimal class each part
    needs, building the node with its graded combinator (`paramArrow`, `paramForall`, the universe combinator) at
    exactly that class. A LEAF (a registered base atom, or a bound type variable) reads its available class and
    WEAKENS down to the demand. No constraint graph, no fixpoint — feasibility is just a stuck `assemble` (a `Type`
    demand above the `(2a,2a)` univalence ceiling, or a leaf that can't weaken to the demand).
  • the TERM half (`assembleTerm`) is the abstraction theorem: `[t u] = [t] u ⟨u⟩ [u]`,
    `[λx:A.t] = fun x x' xR => [t]`, bottoming at registered TERM primitives; every counterpart it needs comes
    from `⟨·⟩`. A PROPOSITION is just a `Sort 0` type — `[P] : PLift (P ↔ P')` is the relator/type witness
    `assemble` builds, projected by `iffOfParam` — so there is no separate `Prop` arm.

BOUND VARIABLES ARE PINNED AT `(4,4)` (type and term alike): a `∀ A : Type` binder offers `A` at inner class
`(4,4)` (the universe combinator's inner relation strength, independent of the capped outer class), and each use
weakens down. This is what removes the fixpoint — a bound variable's class is no longer the join of its uses.

There is ONE relational translation (this file) and ONE term translation (`Translate.term`); the previous
separate "native" pass is gone. `transfer`/`relate` are the type/term entry points.
-/
import LeTrocq.Solver
import LeTrocq.TranslateTerm
import LeTrocq.ParamCC
import Lean
open Lean Lean.Meta
namespace LeTrocq.Transfer
open LeTrocq MapClass LeTrocq.Solver

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
    level `w` is PINNED explicitly (`mkConst … [w]`) because it is phantom in `paramTypeAtInner`'s result —
    no argument carries it, so `mkAppM` could only leave it a free mvar (later wrongly zeroed). -/
def mkUniv (w : Level) (req inner : ParamClass) : MetaM Expr := do
  unless MapClass.le req.1 map2a && MapClass.le req.2 map2a do
    throwError "assemble: `Type` at {repr req} exceeds the universe ceiling (2a) — needs univalence"
  let hm ← leProof req.1 map2a
  let hn ← leProof req.2 map2a
  return mkAppN (mkConst ``paramTypeAtInner [w])
    #[classToExpr req.1, classToExpr req.2, classToExpr inner.1, classToExpr inner.2, hm, hn]

/-- recover `w` from a universe-binder domain `Type w = Sort (w+1)`; a bare `Sort u`/`Prop` domain is out of
    scope for the `Type`-universe path. -/
def typeLevelOf (dom : Expr) : MetaM Level := do
  let .sort l := dom | throwError "assemble: universe-binder domain is not a sort: {dom}"
  match (← instantiateLevelMVars l) with
  | .succ w => return w
  | l       => throwError "assemble: universe binder over `Sort {l}` — only `Type w` domains supported"

/-- the INNER class of every universe combinator: the strength of the `Param p q A A'` a bound type variable is
    offered at. Pinned `(4,4)` (bidir_solver.md): it is the top, independent of the capped outer class, and
    weakens to satisfy every use — which is exactly what lets a bound variable have a fixed class (no fixpoint).
    `paramIdAt (4,4)` is `paramRefl` weakened, so this needs no axiom. -/
def innerClass : ParamClass := (map4, map4)

/- ===================== the graded relational translation `[·]` ===================== -/
/-- the shared `[·]` environment, threaded through EVERY arm (both halves): `fvar ↦ (counterpart x',
    witness-or-relatedness)`. For a TYPE binder the third slot is the bound type's `Param` *witness* at inner
    class `(4,4)` (the leaf rule weakens it to each use; a term-primitive consuming the bound type is fed its
    `.R`); for a TERM binder it is the bare relatedness `xR`. The two never confuse the type/term judgments:
    a type variable's `fvar` has a `Sort` type, a term variable's does not. -/
abbrev SEnv := List (FVarId × Expr × Expr)

/-- project an `SEnv` to the counterpart environment `⟨·⟩` (`Translate.term`) consumes. -/
def SEnv.toTEnv (s : SEnv) : LeTrocq.Translate.TEnv := s.map (fun e => (e.1, e.2.1))

/-- registries + the `⟨·⟩` context, threaded through every arm of `[·]` (built once per top-level call). -/
structure Reg where
  atoms  : NameMap (Expr × Expr × ParamClass)
  consts : NameMap (Expr × ParamClass)
  ctx    : LeTrocq.Translate.Ctx

mutual
/-- `[·]` on a TYPE — the syntax-directed, DEMAND-driven half: walk `T` top-down and build its `Param` witness
    DIRECTLY at the demanded class `dem`, pushing the demand through `depArrow`/`depPi`/`depType` to the minimal
    class each part needs. ONE environment `senv` (`fvar ↦ (counterpart, witness/relatedness)`) is threaded through
    BOTH halves — every in-scope binder, type and term alike, lives there. A relator's TERM arguments go to
    `assembleTerm` (`[t u] = [t] u ⟨u⟩ [u]`). Bound type variables and registered atoms are leaves: they read their
    available class and weaken to `dem`. -/
partial def assemble (reg : Reg) (senv : SEnv) (T : Expr) (dem : ParamClass) : MetaM Expr := do
  match T with
  | .const name _ =>
      -- LEAF: a registered base atom, available at its registered class `regC`; weaken to the demand.
      let some (_, wit, regC) := reg.atoms.find? name | throwError "assemble: atom {name} not registered"
      weakenTo dem regC wit
  | .fvar id =>
      -- LEAF: a bound TYPE variable, offered at inner class `(4,4)`; weaken its witness to the demand.
      let some (_, _, aR) := senv.find? (·.1 == id)
        | throwError "assemble: unbound type variable {T}"
      weakenTo dem innerClass aR
  | .sort lvl => do
      -- `Prop` (Sort 0) reaches the full `(4,4)` via `paramProp` (completeness = `propext`, coherence free by
      -- proof irrelevance); `Type w` (Sort (w+1)) uses the level-`w` universe combinator at `dem`, capped at the
      -- `(2a,2a)` no-univalence ceiling (`mkUniv`), carrying the bound variable at inner class `(4,4)`.
      match (← instantiateLevelMVars lvl) with
      | .zero   => mkAppM ``paramPropAt #[classToExpr dem.1, classToExpr dem.2]
      | .succ w => mkUniv w dem innerClass
      | l       => throwError "assemble: unsupported sort `Sort {l}` (only `Prop` / `Type w`)"
  | .forallE n A B _ => do
      if B.hasLooseBVar 0 then
        match A with
        | .sort _ => do
            -- `∀ A : Type, B` (type-domain Π). Domain via the universe combinator at `depPi(dem).1`, inner `(4,4)`;
            -- codomain family under the binder at `depPi(dem).2`, with `A` recorded in `senv` as a `(4,4)` type var.
            let (domDem, codDem) := depPi dem
            let w ← typeLevelOf A
            let domWit ← mkUniv w domDem innerClass
            let pb ← withLocalDeclD n A fun a =>
              withLocalDeclD (n.appendAfter "'") A fun a' => do
                let raaTy ← mkAppM ``Param.R #[domWit, a, a']
                withLocalDeclD (n.appendAfter "R") raaTy fun aR => do
                  mkLambdaFVars #[a, a', aR]
                    (← assemble reg ((a.fvarId!, a', aR) :: senv) (B.instantiate1 a) codDem)
            mkAppM ``paramForall #[classToExpr dem.1, classToExpr dem.2, domWit, pb]
        | _ => do
            -- `∀ x : T, B` (term-domain Π over ANY buildable domain `T`). Build `T`'s witness at `depPi(dem).1`,
            -- read the two sides `T`/`T'` off its `Param` type, and check the body at `depPi(dem).2` with `x` a
            -- TERM variable whose relatedness is `domWit.R x x'`.
            let (domDem, codDem) := depPi dem
            let domWit ← assemble reg senv A domDem
            let domTy := (← whnf (← instantiateMVars (← inferType domWit))).getAppArgs
            let pb ← withLocalDeclD n domTy[2]! fun x =>
              withLocalDeclD (n.appendAfter "'") domTy[3]! fun x' => do
                let xRTy ← mkAppM ``Param.R #[domWit, x, x']
                withLocalDeclD (n.appendAfter "R") xRTy fun xR => do
                  mkLambdaFVars #[x, x', xR]
                    (← assemble reg ((x.fvarId!, x', xR) :: senv) (B.instantiate1 x) codDem)
            mkAppM ``paramForall #[classToExpr dem.1, classToExpr dem.2, domWit, pb]
      else
        -- `A → B` (non-dependent arrow). Parts at `depArrow(dem)`.
        let (domDem, codDem) := depArrow dem
        mkAppM ``paramArrow
          #[classToExpr dem.1, classToExpr dem.2,
            ← assemble reg senv A domDem,
            ← assemble reg senv (B.instantiate1 (mkConst ``True)) codDem]
  | e@(.app ..) => do
      -- the abstraction theorem `[head a₁ … aₙ] = [head] a₁ ⟨a₁⟩ [a₁] … aₙ ⟨aₙ⟩ [aₙ]`, then WEAKEN to `dem`.
      -- Arguments come from the TERM (`getAppArgs`); routing (type/family/term) from the relator's `relatorArgKinds`.
      -- A TYPE arg's `Param` is assembled at the relator's declared arg class; a FAMILY arg's is the `Param` family
      -- `fun a a' aR => ⟨B a ≃ B' a'⟩`; a TERM arg's `(⟨aᵢ⟩, [aᵢ])` come from the term-half `⟨·⟩`/`[·]` over `senv`.
      let some head := e.getAppFn.constName? | throwError "assemble: application head {e.getAppFn} is not a constant"
      let some (relator, relClass) := reg.consts.find? head | throwError "assemble: constant {head} not registered"
      let kinds ← relatorArgKinds relator
      let args := e.getAppArgs
      unless args.size == kinds.size do
        throwError "assemble: relator {head} takes {kinds.size} arguments but is applied to {args.size}"
      let mut argExprs : Array Expr := #[]
      let mut argWits : Array (Option Expr) := Array.replicate args.size none  -- each TYPE arg's witness, by index
      for i in [0 : args.size] do
        let arg := args[i]!
        match kinds[i]! with
        | .type cls => do                                  -- TYPE arg: build its `Param` at the relator's class
            let tR ← assemble reg senv arg cls
            let tgt := (← whnf (← instantiateMVars (← inferType tR))).getAppArgs[3]!
            argExprs := argExprs ++ #[arg, tgt, tR]
            argWits := argWits.set! i (some tR)
        | .family cls domIdx => do                         -- FAMILY arg: build the `Param` family + its B-side
            let some paWit := argWits[domIdx]!
              | throwError "assemble: family argument {i} of {head} has no domain type argument (#{domIdx})"
            let paTy := (← whnf (← instantiateMVars (← inferType paWit))).getAppArgs
            let (famB', pbWit) ← withLocalDeclD `a paTy[2]! fun a => withLocalDeclD `a' paTy[3]! fun a' => do
              let aRTy ← mkAppM ``Param.R #[paWit, a, a']
              withLocalDeclD `aR aRTy fun aR => do
                let bodyWit ← assemble reg ((a.fvarId!, a', aR) :: senv) (arg.beta #[a]) cls
                -- the B-side family `B' : A' → Type` must depend only on `a'`, never on `a`/`aR`.
                let bside := (← whnf (← instantiateMVars (← inferType bodyWit))).getAppArgs[3]!
                if bside.hasAnyFVar (fun id => id == a.fvarId! || id == aR.fvarId!) then
                  throwError "assemble: family B-side depends on the element/proof — unsupported dependent family in {head}"
                return (← mkLambdaFVars #[a'] bside, ← mkLambdaFVars #[a, a', aR] bodyWit)
            argExprs := argExprs ++ #[arg, famB', pbWit]
        | .term => do                                      -- TERM arg: counterpart `⟨a⟩` + relatedness `[a]`
            let a' ← LeTrocq.Translate.term reg.ctx senv.toTEnv arg
            let aR ← assembleTerm reg senv arg
            argExprs := argExprs ++ #[arg, a', aR]
      weakenTo dem relClass (mkAppN relator argExprs)
  | e => throwError "assemble: unsupported type {e}"

/-- `[·]` on a TYPE embedded in a term: its `Param` witness, at the trivial class `(0,0)` — a term position
    consumes only the relation `.R`, which is grade-invariant, so the cheapest class suffices. The ambient `senv`
    is threaded in so a DEPENDENT type resolves — e.g. `Boxed b` / `Vec n` with `b`/`n` bound by an outer λ (the
    bound term supplies its relatedness), or a type over an outer λ-bound TYPE variable (its `(4,4)` witness sits
    in `senv`, and `assemble`'s leaf rule weakens it). -/
partial def assembleType (reg : Reg) (senv : SEnv) (T : Expr) : MetaM Expr :=
  assemble reg senv T (map0, map0)

/-- `〚·〛 := [·].R` (DESIGN.md's `〚A〛 := A.R`): the RELATION of a type `T`, projected off the graded witness
    `[·]` (`assembleType`) builds. All a TERM position ever consumes of a type, and grade-invariant — so
    `assembleType`'s cheapest `(0,0)` witness suffices. -/
partial def assembleRel (reg : Reg) (senv : SEnv) (T : Expr) : MetaM Expr := do
  mkAppM ``Param.R #[← assembleType reg senv T]

/-- `[·]` on a TERM (the abstraction theorem): its relatedness `[e] : 〚T〛 e ⟨e⟩`. Counterparts `⟨·⟩` come
    from `Translate.term`; a TYPE-valued sub-term contributes its relation `(assembleType …).R`. A PROPOSITION
    `P` is just a `Sort 0` type: its relatedness `[P] : 〚Prop〛 P P' = PLift (P ↔ P')` is the `(1,1)` `Param`
    witness the relator path builds, projected via `iffOfParam` — no separate `Prop` arm. Bottoms out at
    registered TERM primitives (`ctx.terms`). -/
partial def assembleTerm (reg : Reg) (senv : SEnv) (e : Expr) : MetaM Expr := do
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
          let w ← assemble reg senv e (map1, map1)
          return ← mkAppM ``PLift.up #[← mkAppM ``iffOfParam #[w]]
    else return ← assembleRel reg senv e
  if let some n := LeTrocq.Translate.natNumeral? e then
    if (← whnf ty).isConstOf ``Nat then return ← assembleTerm reg senv (LeTrocq.Translate.natExpr n)
  match e with
  | .fvar id =>
      match senv.find? (·.1 == id) with
      | some (_, _, xR) => return xR
      | none => throwError "assemble: unbound variable {e}"
  | .const c _ =>
      match reg.ctx.terms.find? c with
      | some (_, wit) => return wit
      | none => throwError "assemble: unregistered constant {c}"
  | .app f a => do
      let fR ← assembleTerm reg senv f
      let a' ← LeTrocq.Translate.term reg.ctx senv.toTEnv a
      let aR ← assembleTerm reg senv a
      return mkApp3 fR a a' aR
  | .lam n A b _ => do
      let A' ← LeTrocq.Translate.term reg.ctx senv.toTEnv A
      -- the bound variable's relatedness is `〚A〛 = [A].R`: for a type binder the parametricity relation, for
      -- a term/base binder the bare relatedness. (`assembleRel` projects it off the graded witness `[A]`.)
      let relA ← assembleRel reg senv A
      withLocalDeclD n A fun x =>
      withLocalDeclD (n.appendAfter "'") A' fun x' =>
      withLocalDeclD (n.appendAfter "R") (mkApp2 relA x x') fun xR => do
        mkLambdaFVars #[x, x', xR]
          (← assembleTerm reg ((x.fvarId!, x', xR) :: senv) (b.instantiate1 x))
  | e => throwError "assemble: unsupported term {e}"
end

/-- the registries + `⟨·⟩` context, built once from the `@[trocq]` environment extension. -/
def mkReg : MetaM Reg := do
  return { atoms := ← Solver.buildAtoms, consts := ← Solver.buildConsts, ctx := ← LeTrocq.Translate.buildCtx }

/-- default any genuinely-free residual universe mvars (e.g. the universe combinator's relation level, or a
    universe-poly registered witness's level) to 0 — they are unconstrained, so any level is sound. -/
def defaultFreeLevels (wit : Expr) : MetaM Expr := do
  let wit ← instantiateMVars wit
  let st := Lean.collectLevelMVars (Lean.collectLevelMVars {} wit) (← instantiateMVars (← inferType wit))
  for mid in st.result do
    unless (← isLevelMVarAssigned mid) do assignLevelMVar mid levelZero
  instantiateMVars wit

/-- `[T]@root` for a TYPE: assemble the witness DIRECTLY at `root` in one demand-driven pass — every node built
    by the graded combinator at the minimal class the demand pushes down. Drives `transfer%`/`trocq`. -/
partial def transfer (e : Expr) (root : ParamClass) : MetaM Expr := do
  defaultFreeLevels (← assemble (← mkReg) [] e root)

/-- `[t]` for a TERM: its relatedness by the abstraction theorem. Drives `relate%`. -/
partial def relate (e : Expr) : MetaM Expr := do
  defaultFreeLevels (← assembleTerm (← mkReg) [] e)

end LeTrocq.Transfer
