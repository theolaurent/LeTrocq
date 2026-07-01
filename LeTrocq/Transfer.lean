/-
THE GRADED RELATIONAL TRANSLATION `[·]` (DESIGN.md's `[·]`): produce the relatedness witness
`[e] : 〚T〛 e ⟨e⟩` (with `〚T〛 := [T].R`), relying on the one term translation `⟨·⟩` (`LeTrocq.Translate.term`).

It has two mutually-recursive halves — as DESIGN.md itself splits `[Πx:A.B]` from `[t u]`:

  • the TYPE half (`assemble`) is graded: driven by the `GradedShape` the solver (`LeTrocq.Solver`) inferred,
    it walks `(term, gradedShape)` IN LOCKSTEP and dispatches each type-former node to its graded combinator
    (`paramArrow`, `paramForall`, the universe combinator), asking each part only at the class the shape
    already resolved (`node.cls`) — it never re-derives a grade. `assembleType` is its entry for a type
    embedded in a term (a bound type variable, or a closed type graded fresh at the trivial `(0,0)`, since a
    term position consumes only the grade-invariant relation `.R`).
  • the TERM half (`assembleTerm`/`assembleProp`) is the abstraction theorem: `[t u] = [t] u ⟨u⟩ [u]`,
    `[λx:A.t] = fun x x' xR => [t]`, bottoming at registered TERM/PROP primitives; every counterpart it
    needs comes from `⟨·⟩`.

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

/-- the universe combinator at outer class `req`, carrying inner relation class `inner`. -/
def mkUniv (req inner : ParamClass) : MetaM Expr := do
  unless MapClass.le req.1 map2a && MapClass.le req.2 map2a do
    throwError "assemble: `Type` at {repr req} exceeds the universe ceiling (2a) — needs univalence"
  mkAppM ``paramTypeAtInner #[classToExpr req.1, classToExpr req.2, classToExpr inner.1,
    classToExpr inner.2, ← leProof req.1 map2a, ← leProof req.2 map2a]

/- ===================== the graded relational translation `[·]` ===================== -/
/-- the term-half env: `fvar ↦ (counterpart x', witness-or-relatedness)`. For a TYPE binder the third slot is
    the bound type's `Param` *witness* (`assembleType` returns it; a term-primitive consuming the bound type
    is fed its `.R`); for a TERM binder it is the bare relatedness `xR`. -/
abbrev SEnv := List (FVarId × Expr × Expr)

/-- project an `SEnv` to the counterpart environment `⟨·⟩` (`Translate.term`) consumes. -/
def SEnv.toTEnv (s : SEnv) : LeTrocq.Translate.TEnv := s.map (fun e => (e.1, e.2.1))

/-- registries + the `⟨·⟩` context, threaded through every arm of `[·]` (built once per top-level call). -/
structure Reg where
  atoms  : NameMap (Expr × Expr × ParamClass)
  consts : NameMap (Expr × ParamClass)
  ctx    : LeTrocq.Translate.Ctx

mutual
/-- `[·]` on a TYPE — the graded, `GradedShape`-driven half: build the `Param` witness node by node, each at
    the class the solver resolved (`node.cls`), no re-inference. `env` maps a Π/type-binder's `bId` to its
    bound type variable's `(A, A', aR, srcCls)` (relatedness `aR : Param srcCls A A'`, and the class it sits
    at, for weakening a use down to its local grade); `termEnv` maps a term-binder's `bId` to `(x, x', xR)`.
    A relator's TERM arguments are handed to the term-half `assembleTerm` (`[t u] = [t] u ⟨u⟩ [u]`). -/
partial def assemble (reg : Reg)
    (env : List (Nat × (Expr × Expr × Expr × ParamClass)))
    (termEnv : List (Nat × (Expr × Expr × Expr))) (term : Expr) : GradedShape → MetaM Expr
  | .atom cls name => do
      let some (_, wit, regC) := reg.atoms.find? name | throwError "assemble: atom {name} not registered"
      weakenTo cls regC wit
  | .usevar cls bId => do
      let some (_, _, _, aR, src) := env.find? (·.1 == bId)
        | throwError "assemble: bound type variable (bId {bId}) not in scope"
      -- the universe combinator supplied the bound var's witness at its solved class `src`; weaken to the use.
      weakenTo cls src aR
  | .sort cls inner => mkUniv cls inner
  | .arrow cls dom cod => do
      let .forallE _ A B _ := term | throwError "assemble: arrow shape but term is {term}"
      mkAppM ``paramArrow
        #[classToExpr cls.1, classToExpr cls.2,
          ← assemble reg env termEnv A dom,
          ← assemble reg env termEnv (B.instantiate1 (mkConst ``True)) cod]
  | .pi cls domCls inner bId body => do
      let .forallE _ _ B _ := term | throwError "assemble: pi shape but term is {term}"
      -- the domain `Type` carries the bound variable at its solved inner class (the `Map_Type` inner).
      let domWit ← mkUniv domCls inner
      -- codomain FAMILY: fun (A A' : Type) (aR : domWit.R A A') => ⟨body witness, with bId ↦ (A,A',aR)⟩
      let pb ← withLocalDeclD `A (.sort (.succ .zero)) fun A =>
        withLocalDeclD `A' (.sort (.succ .zero)) fun A' => do
          let raaTy ← mkAppM ``Param.R #[domWit, A, A']
          withLocalDeclD `aR raaTy fun aR => do
            mkLambdaFVars #[A, A', aR]
              (← assemble reg ((bId, (A, A', aR, inner)) :: env) termEnv (B.instantiate1 A) body)
      mkAppM ``paramForall #[classToExpr cls.1, classToExpr cls.2, domWit, pb]
  | .piTerm cls bId dom body => do
      let .forallE _ A B _ := term | throwError "assemble: piTerm shape but term is {term}"
      -- build `T`'s witness from its sub-shape, read the two sides `T`/`T'` off its `Param` type (`whnf`
      -- first — a weaken-free witness can carry a projection rather than a bare `Param … T T'`).
      let domWit ← assemble reg env termEnv A dom
      let domTy := (← whnf (← instantiateMVars (← inferType domWit))).getAppArgs
      let pb ← withLocalDeclD `x domTy[2]! fun x =>
        withLocalDeclD `x' domTy[3]! fun x' => do
          let xRTy ← mkAppM ``Param.R #[domWit, x, x']
          withLocalDeclD `xR xRTy fun xR => do
            mkLambdaFVars #[x, x', xR]
              (← assemble reg env ((bId, (x, x', xR)) :: termEnv) (B.instantiate1 x) body)
      mkAppM ``paramForall #[classToExpr cls.1, classToExpr cls.2, domWit, pb]
  | .app cls head gargs => do
      -- the abstraction theorem `[head a₁ … aₙ] = [head] a₁ ⟨a₁⟩ [a₁] … aₙ ⟨aₙ⟩ [aₙ]`. Arguments come from
      -- the TERM (`getAppArgs`); routing (type/family/term) from the shape. A TYPE arg's `Param` is built by
      -- recursively assembling its sub-shape; a FAMILY arg's is the `Param` family `fun a a' aR => ⟨B a ≃ B' a'⟩`;
      -- a TERM arg's `(⟨aᵢ⟩, [aᵢ])` come from the term-half `⟨·⟩`/`[·]`. Then weaken the whole to `cls`.
      let some (relator, relClass) := reg.consts.find? head | throwError "assemble: constant {head} not registered"
      -- the in-scope binders as an `SEnv` for the term-half: term binders `x ↦ (x', xR)`, type binders
      -- `A ↦ (A', aR)` (the WITNESS; `assembleTerm`/`⟨·⟩` project `.R`/take `x'` as needed).
      let mut senv : SEnv := []
      for (_, x, x', xR) in termEnv do senv := (x.fvarId!, x', xR) :: senv
      for (_, A, A', aR, _) in env do senv := (A.fvarId!, A', aR) :: senv
      let args := term.getAppArgs
      let gargsArr := gargs.toArray
      let mut argExprs : Array Expr := #[]
      let mut argWits : Array (Option Expr) := Array.replicate args.size none  -- each TYPE arg's witness, by index
      for i in [0 : args.size] do
        let arg := args[i]!
        match gargsArr[i]! with
        | .type sub =>                                     -- TYPE arg: build its `Param` from the sub-shape
            let tR ← assemble reg env termEnv arg sub
            let tgt := (← whnf (← instantiateMVars (← inferType tR))).getAppArgs[3]!
            argExprs := argExprs ++ #[arg, tgt, tR]
            argWits := argWits.set! i (some tR)
        | .family elemBid domIdx sub =>                    -- FAMILY arg: build the `Param` family + its B-side
            let some paWit := argWits[domIdx]!
              | throwError "assemble: family argument {i} of {head} has no domain type argument (#{domIdx})"
            let paTy := (← whnf (← instantiateMVars (← inferType paWit))).getAppArgs
            let (famB', pbWit) ← withLocalDeclD `a paTy[2]! fun a => withLocalDeclD `a' paTy[3]! fun a' => do
              let aRTy ← mkAppM ``Param.R #[paWit, a, a']
              withLocalDeclD `aR aRTy fun aR => do
                let bodyWit ← assemble reg env ((elemBid, (a, a', aR)) :: termEnv) (arg.beta #[a]) sub
                -- the B-side family `B' : A' → Type` must depend only on `a'`, never on `a`/`aR`.
                let bside := (← whnf (← instantiateMVars (← inferType bodyWit))).getAppArgs[3]!
                if bside.hasAnyFVar (fun id => id == a.fvarId! || id == aR.fvarId!) then
                  throwError "assemble: family B-side depends on the element/proof — unsupported dependent family in {head}"
                return (← mkLambdaFVars #[a'] bside, ← mkLambdaFVars #[a, a', aR] bodyWit)
            argExprs := argExprs ++ #[arg, famB', pbWit]
        | .term =>                                         -- TERM arg: counterpart `⟨a⟩` + relatedness `[a]`
            let a' ← LeTrocq.Translate.term reg.ctx senv.toTEnv arg
            let aR ← assembleTerm reg senv arg
            argExprs := argExprs ++ #[arg, a', aR]
      weakenTo cls relClass (mkAppN relator argExprs)

/-- `[·]` on a TYPE embedded in a term: its `Param` witness. A bound type variable resolves from the env;
    any other (closed) type is graded fresh at the trivial class `(0,0)` — its relation `.R` is all a term
    position consumes, and `.R` is invariant under the grade, so the cheapest class suffices. -/
partial def assembleType (reg : Reg) (senv : SEnv) (T : Expr) : MetaM Expr := do
  match T with
  | .fvar id =>
      match senv.find? (·.1 == id) with
      | some (_, _, w) => return w
      | none => throwError "assemble: unbound type variable {T}"
  | _ =>
      let gs ← Solver.gradeShape T (map0, map0)
      assemble reg [] [] T gs

/-- `[·]` on a TERM (the abstraction theorem): its relatedness `[e] : 〚T〛 e ⟨e⟩`. Counterparts `⟨·⟩` come
    from `Translate.term`; a TYPE-valued sub-term contributes its relation `(assembleType …).R`; a `Prop`
    goes through `assembleProp`. Bottoms out at registered TERM primitives (`ctx.terms`). -/
partial def assembleTerm (reg : Reg) (senv : SEnv) (e : Expr) : MetaM Expr := do
  let ty ← inferType e
  if let .sort lvl := ty then
    if (← instantiateLevelMVars lvl) == levelZero then return ← assembleProp reg senv e
    else return ← mkAppM ``Param.R #[← assembleType reg senv e]
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
      -- the bound variable's relatedness lives in `[A].R` (= `〚A〛`): for a type binder the parametricity
      -- relation, for a term/base binder the bare relatedness. `[A]` is the graded witness (via `assembleType`).
      let relA ← mkAppM ``Param.R #[← assembleType reg senv A]
      withLocalDeclD n A fun x =>
      withLocalDeclD (n.appendAfter "'") A' fun x' =>
      withLocalDeclD (n.appendAfter "R") (mkApp2 relA x x') fun xR => do
        mkLambdaFVars #[x, x', xR]
          (← assembleTerm reg ((x.fvarId!, x', xR) :: senv) (b.instantiate1 x))
  | e => throwError "assemble: unsupported term {e}"

/-- `[·]` on a PROPOSITION: its logical-equivalence relatedness `PLift (P ↔ P')`. Connectives combine their
    parts congruently; a registered predicate `p` supplies its own (`[p a₁…] = pR a₁ ⟨a₁⟩ [a₁] …`). -/
partial def assembleProp (reg : Reg) (senv : SEnv) (P : Expr) : MetaM Expr := do
  let args := P.getAppArgs
  match P.getAppFn with
  | .const c _ =>
      if (c == ``True || c == ``False) && args.isEmpty then
        mkAppM ``PLift.up #[← mkAppOptM ``Iff.rfl #[P]]
      else if c == ``Not && args.size == 1 then
        mkAppM ``PLift.up #[← mkAppM ``not_congr
          #[← mkAppM ``PLift.down #[← assembleProp reg senv args[0]!]]]
      else if (c == ``And || c == ``Or || c == ``Iff) && args.size == 2 then
        let hL ← assembleProp reg senv args[0]!
        let hR ← assembleProp reg senv args[1]!
        let cong := if c == ``And then ``and_congr else if c == ``Or then ``or_congr else ``iff_congr
        mkAppM ``PLift.up #[← mkAppM cong
          #[← mkAppM ``PLift.down #[hL], ← mkAppM ``PLift.down #[hR]]]
      else match reg.ctx.props.find? c with
        | some (_, wit) =>
            -- the abstraction theorem for a registered predicate `p`: `[p a₁ … aₙ] = pR a₁ ⟨a₁⟩ [a₁] …`.
            let mut rel := wit
            for a in args do
              rel := mkApp3 rel a (← LeTrocq.Translate.term reg.ctx senv.toTEnv a) (← assembleTerm reg senv a)
            return rel
        | none => throwError "assemble: unregistered/opaque proposition head {c}"
  | f => throwError "assemble: unsupported proposition (head {f})"
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

/-- `[T]@root` for a TYPE: solve for the grading, then assemble the witness DIRECTLY at `root` — every node
    built by the graded combinator at the class the solver's annotations dictate. Drives `transfer%`/`trocq`. -/
partial def transfer (e : Expr) (root : ParamClass) : MetaM Expr := do
  let gs ← Solver.gradeShape e root
  defaultFreeLevels (← assemble (← mkReg) [] [] e gs)

/-- `[t]` for a TERM: its relatedness by the abstraction theorem. Drives `relate%`. -/
partial def relate (e : Expr) : MetaM Expr := do
  defaultFreeLevels (← assembleTerm (← mkReg) [] e)

end LeTrocq.Transfer
