/-
THE GRADED TRANSLATION: build the witness from the original term + the solver's annotations.

Given the original type `e` and the `GradedShape` the solver (`LeTrocq.Solver`) inferred for it, `assemble`
walks `(term, gradedShape)` IN LOCKSTEP — every subterm comes from the term, every grade and routing
decision from the shape — and dispatches each node to its graded combinator (`paramArrow`, `paramForall`,
the universe combinator), asking each part only at the class the shape already resolved. It is the graded
form of DESIGN.md's `〚·〛`: the type-former translation, indexed by the grading.

The split from the solver is exactly the input: this half never re-derives a class or re-walks to infer
one — it reads `node.cls` off the annotated shape. What it needs from the term (and NOT the shape) are the
actual subterms: an arrow's domain/codomain, a Π's body, and a relator application's ARGUMENTS — a TERM
argument's counterpart+relatedness come from the native term translation (`LeTrocq.Translate.param`), read
straight off the term with no closure round-trip.
-/
import LeTrocq.Solver
import LeTrocq.Translate
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

/- ===================== the graded translation ===================== -/
/-- build the witness by walking `(term, gs)` in lockstep. `env` maps a Π/type-binder's `bId` to its bound
    type variable's `(A, A', aR, srcCls)` — source/target type, relatedness `aR : Param srcCls A A'`, and
    the class `aR` sits at (for weakening a use down to its local grade); `termEnv` maps a term-binder's
    `bId` to `(x, x', xR)`. Each node's grade is read straight off `gs` (`node.cls`) — no re-inference. -/
partial def assemble (atoms : NameMap (Expr × Expr × ParamClass)) (consts : NameMap (Expr × ParamClass))
    (env : List (Nat × (Expr × Expr × Expr × ParamClass)))
    (termEnv : List (Nat × (Expr × Expr × Expr))) (term : Expr) : GradedShape → MetaM Expr
  | .atom cls name => do
      let some (_, wit, reg) := atoms.find? name | throwError "assemble: atom {name} not registered"
      weakenTo cls reg wit
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
          ← assemble atoms consts env termEnv A dom,
          ← assemble atoms consts env termEnv (B.instantiate1 (mkConst ``True)) cod]
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
              (← assemble atoms consts ((bId, (A, A', aR, inner)) :: env) termEnv (B.instantiate1 A) body)
      mkAppM ``paramForall #[classToExpr cls.1, classToExpr cls.2, domWit, pb]
  | .piTerm cls bId dom body => do
      let .forallE _ A B _ := term | throwError "assemble: piTerm shape but term is {term}"
      -- build `T`'s witness from its sub-shape, read the two sides `T`/`T'` off its `Param` type (`whnf`
      -- first — a weaken-free witness can carry a projection rather than a bare `Param … T T'`).
      let domWit ← assemble atoms consts env termEnv A dom
      let domTy := (← whnf (← instantiateMVars (← inferType domWit))).getAppArgs
      let pb ← withLocalDeclD `x domTy[2]! fun x =>
        withLocalDeclD `x' domTy[3]! fun x' => do
          let xRTy ← mkAppM ``Param.R #[domWit, x, x']
          withLocalDeclD `xR xRTy fun xR => do
            mkLambdaFVars #[x, x', xR]
              (← assemble atoms consts env ((bId, (x, x', xR)) :: termEnv) (B.instantiate1 x) body)
      mkAppM ``paramForall #[classToExpr cls.1, classToExpr cls.2, domWit, pb]
  | .app cls head gargs => do
      -- the abstraction theorem `⟦head a₁ … aₙ⟧ = ⟦head⟧ a₁ a₁' a₁R … aₙ aₙ' aₙR`. Arguments come from the
      -- TERM (`getAppArgs`); routing (type/family/term) from the shape. A TERM arg's `(aᵢ', aᵢR)` come from
      -- the native term translation; a TYPE arg's from recursively assembling its sub-shape; a FAMILY arg's
      -- relatedness is the `Param` family `fun a a' aR => ⟨B a ≃ B' a'⟩`. Then weaken the whole to `cls`.
      let some (relator, relClass) := consts.find? head | throwError "assemble: constant {head} not registered"
      let ctx ← LeTrocq.Translate.buildCtx
      -- the in-scope binders' translation env: term binders `x ↦ (x', xR)`, type binders `A ↦ (A', Param.R aR)`.
      let mut transEnv : LeTrocq.Translate.Env := []
      for (_, x, x', xR) in termEnv do transEnv := (x.fvarId!, x', xR) :: transEnv
      for (_, A, A', aR, _) in env do transEnv := (A.fvarId!, A', ← mkAppM ``Param.R #[aR]) :: transEnv
      let args := term.getAppArgs
      let gargsArr := gargs.toArray
      let mut argExprs : Array Expr := #[]
      let mut argWits : Array (Option Expr) := Array.replicate args.size none  -- each TYPE arg's witness, by index
      for i in [0 : args.size] do
        let arg := args[i]!
        match gargsArr[i]! with
        | .type sub =>                                     -- TYPE arg: build its `Param` from the sub-shape
            let tR ← assemble atoms consts env termEnv arg sub
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
                let bodyWit ← assemble atoms consts env ((elemBid, (a, a', aR)) :: termEnv) (arg.beta #[a]) sub
                -- the B-side family `B' : A' → Type` must depend only on `a'`, never on `a`/`aR`.
                let bside := (← whnf (← instantiateMVars (← inferType bodyWit))).getAppArgs[3]!
                if bside.hasAnyFVar (fun id => id == a.fvarId! || id == aR.fvarId!) then
                  throwError "assemble: family B-side depends on the element/proof — unsupported dependent family in {head}"
                return (← mkLambdaFVars #[a'] bside, ← mkLambdaFVars #[a, a', aR] bodyWit)
            argExprs := argExprs ++ #[arg, famB', pbWit]
        | .term =>                                         -- TERM arg: native counterpart + relatedness
            let (a', aR) ← LeTrocq.Translate.param ctx transEnv arg
            argExprs := argExprs ++ #[arg, a', aR]
      weakenTo cls relClass (mkAppN relator argExprs)

/-- full pipeline: solve for the grading, then assemble the witness DIRECTLY at `root` — every node built
    by the graded combinator at the class the solver's annotations dictate (parts never over-provisioned). -/
partial def transfer (e : Expr) (root : ParamClass) : MetaM Expr := do
  let gs ← Solver.gradeShape e root
  let wit ← instantiateMVars (← assemble (← Solver.buildAtoms) (← Solver.buildConsts) [] [] e gs)
  -- default any genuinely-free residual universe mvars (e.g. the universe combinator's relation level, or a
  -- universe-poly registered witness's level) to 0 — they're unconstrained, so any level is sound.
  let st := Lean.collectLevelMVars (Lean.collectLevelMVars {} wit) (← instantiateMVars (← inferType wit))
  for mid in st.result do
    unless (← isLevelMVarAssigned mid) do assignLevelMVar mid levelZero
  instantiateMVars wit

end LeTrocq.Transfer
