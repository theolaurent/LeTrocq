/-
THE DRIVER: solver-directed witness assembly. Two passes over a type `Expr`.

  FRONT HALF (`gen` + `runSolve`):
    walk the type, assign a class `Var` to every node, emit the `Cstr` edges
    (`depArrow`/`depPi`/`depType`/`gev` from `Lattice`), seed the root, and run `Trocq.solve`.
    Output: the MINIMAL class each occurrence needs. Reproduces the paper's `∀A:Type, A→A`
    inference *from the actual Expr* (domain `Type` → (2a,0), bound `A` → (1,1)).

  BACK HALF (`assemble`):
    rebuild the witness by dispatching each node to its graded combinator (`paramArrow`, `paramForall`,
    the universe combinator), asking each part only at the `dep*`-minimal class it needs, and weakening
    the registered base leaves to fit. Handles arrows, polymorphic `∀ A : Type`, dependent Π over a
    registered base, and the generic application node (the abstraction theorem
    `⟦head x₁ … xₙ⟧ = ⟦head⟧ x₁ x₁' x₁R … xₙ xₙ' xₙR`, for a relator `head` applied to bound base variables).

The registered bases / relators come from the `@[trocq]` extension (`buildAtoms`/`buildConsts`).
-/
import Trocq.Combinators
import Trocq.Attr
import Lean
open Lean Lean.Meta
namespace Trocq.Solver
open Trocq MapClass

/- ===================== constraint-generation state ===================== -/
structure GenState where
  next        : Nat := 0
  cstrs       : Array Cstr := #[]
  binders     : List (FVarId × Nat) := []   -- type-variable binders (`∀ A : Type`) → their class var
  termBinders : List (FVarId × Nat) := []   -- term-variable binders (`∀ x : Base`) → their binder id

/-- shape tree: each node remembers its class `Var`. -/
inductive Shape
  | atom   (v : Nat) (name : Name)
  | arrow  (v : Nat) (dom cod : Shape)
  | pi     (v domV rV : Nat) (body : Shape)              -- `∀ A : Type, …`
  | sort   (v rV : Nat)
  | usevar (v rV : Nat)                                  -- use of a bound TYPE variable
  | piBase (v bId : Nat) (base : Name) (body : Shape)    -- `∀ (x : base), …` over a registered base
  | app    (v : Nat) (head : Name) (argBids : List Nat)  -- `head x₁ … xₙ`, registered `head` on term-binders

def Shape.var : Shape → Nat
  | .atom v _ | .arrow v _ _ | .pi v _ _ _ | .sort v _ | .usevar v _ | .piBase v _ _ _ | .app v _ _ => v

/- ===================== front half: generate constraints from a type Expr ===================== -/
partial def gen (atoms : NameMap (Expr × Expr × ParamClass)) (consts : NameMap (Expr × ParamClass))
    (st : IO.Ref GenState) : Expr → MetaM Shape
  | .forallE n A B _ => do
      if B.hasLooseBVar 0 then
        match A with
        | .sort _ =>                                       -- ∀ (A : Type), … (a type binder)
            let v ← fresh; let domV ← fresh; let rV ← fresh
            emit (.depType domV rV)
            withLocalDeclD n A fun x => do
              st.modify fun s => { s with binders := (x.fvarId!, rV) :: s.binders }
              let sb ← gen atoms consts st (B.instantiate1 x)
              emit (.depPi v domV sb.var)
              return .pi v domV rV sb
        | .const baseName _ =>                             -- ∀ (x : Base), … over a registered base
            unless atoms.contains baseName do throwError "gen: dependent Π over unregistered base {baseName}"
            let v ← fresh; let domV ← fresh; let bId ← fresh
            withLocalDeclD n A fun x => do
              st.modify fun s => { s with termBinders := (x.fvarId!, bId) :: s.termBinders }
              let sb ← gen atoms consts st (B.instantiate1 x)
              emit (.depPi v domV sb.var)
              return .piBase v bId baseName sb
        | _ => throwError "gen: dependent Π over non-Type/base unsupported"
      else
        let v ← fresh
        let sd ← gen atoms consts st A
        let sc ← gen atoms consts st (B.instantiate1 (mkConst ``True))
        emit (.depArrow v sd.var sc.var)
        return .arrow v sd sc
  | e@(.app ..) => do                                     -- `head x₁ … xₙ`: registered relator on bound term vars
      let some head := e.getAppFn.constName?
        | throwError "gen: application head {e.getAppFn} is not a constant"
      unless consts.contains head do throwError "gen: unregistered relator {head}"
      let bids ← e.getAppArgs.toList.mapM fun arg => do
        let .fvar x := arg
          | throwError "gen: relator argument {arg} is not a bound base variable (nested apps unsupported)"
        match (← st.get).termBinders.find? (·.1 == x) with
        | some (_, bId) => pure bId
        | none => throwError "gen: relator argument is not a registered base variable"
      let v ← fresh; return .app v head bids
  | .const name _ => do
      let v ← fresh
      if atoms.contains name then return .atom v name
      else throwError "gen: unregistered base atom {name}"
  | .sort _ => do
      let v ← fresh; let rV ← fresh; emit (.depType v rV); return .sort v rV
  | .fvar id => do
      match (← st.get).binders.find? (·.1 == id) with
      | some (_, bv) => let p ← fresh; emit (.gev bv p); return .usevar p bv
      | none => throwError "gen: unbound fvar"
  | e => throwError "gen: unsupported {e}"
where
  fresh : MetaM Nat := do let s ← st.get; st.set { s with next := s.next + 1 }; return s.next
  emit (c : Cstr) : MetaM Unit := st.modify fun s => { s with cstrs := s.cstrs.push c }

/- ===================== registries from the `@[trocq]` extension ===================== -/
/-- type-atom registry from every `@[trocq]` BASE, BOTH directions (the base and its `Param.sym`), so a
    type built over either side of an equivalence resolves by head match. -/
def buildAtoms : MetaM (NameMap (Expr × Expr × ParamClass)) := do
  let mut m := mkNameMap _
  for e in trocqEntries (← getEnv) do
    if let .base hA hB tyA tyB wit cls := e then
      m := m.insert hA (tyB, wit, cls)
      m := m.insert hB (tyA, ← mkAppM ``Param.sym #[wit], (cls.2, cls.1))
  return m

/-- constant registry from every `@[trocq]` RELATOR (keyed by the applied head, as written). -/
def buildConsts : MetaM (NameMap (Expr × ParamClass)) := do
  let mut m := mkNameMap _
  for e in trocqEntries (← getEnv) do
    if let .relator hA wit cls := e then m := m.insert hA (wit, cls)
  return m

/-- run the front half (build registries, generate constraints, solve): shape + minimal class per `Var`. -/
def runSolve (e : Expr) (root : ParamClass) : MetaM (Shape × Array ParamClass) := do
  let st ← IO.mkRef {}
  let shape ← gen (← buildAtoms) (← buildConsts) st e
  let s ← st.get
  return (shape, Trocq.solve s.next [(shape.var, root)] s.cstrs.toList)

/- ===================== back half: assemble the witness from combinators + weakening ===================== -/
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

/-- assemble a witness AT the requested class `req`, dispatching each former to its graded combinator
    and asking each part only at the `dep*`-minimal class it needs — no over-provisioning.
    `env` maps a Π-binder's class var to the in-scope relatedness witness for that bound type variable;
    `sol` supplies each binder's solved (`Map_Type`-inner) class. -/
partial def assemble (atoms : NameMap (Expr × Expr × ParamClass)) (consts : NameMap (Expr × ParamClass))
    (sol : Array ParamClass) (env : List (Nat × Expr)) (termEnv : List (Nat × (Expr × Expr × Expr)))
    (req : ParamClass) : Shape → MetaM Expr
  | .atom _ name => do
      let some (_, wit, reg) := atoms.find? name | throwError "assemble: atom {name} not registered"
      weakenTo req reg wit
  | .usevar _ rV => do
      let some (_, aR) := env.find? (·.1 == rV)
        | throwError "assemble: bound type variable (var {rV}) not in scope"
      -- the universe combinator supplies the bound var at its solved class `sol[rV]`; weaken to the use.
      weakenTo req sol[rV]! aR
  | .sort _ rV => mkUniv req sol[rV]!
  | .arrow _ sd sc => do
      let (da, dc) := depArrow req            -- the minimal domain/codomain classes for this output
      mkAppM ``paramArrow
        #[classToExpr req.1, classToExpr req.2,
          ← assemble atoms consts sol env termEnv da sd, ← assemble atoms consts sol env termEnv dc sc]
  | .pi _ _ rV body => do
      -- `paramForall` is fully graded; for `∀ A : Type` the effective cap is enforced by `mkUniv` below
      -- (the universe domain `Type` is capped at `2a` by univalence — see the `dPi` build).
      let (dPi, cPi) := depPi req              -- domain (`Type`) class, codomain (body) class
      -- the domain `Type` carries the bound variable at its solved class `sol[rV]` (the `Map_Type` inner).
      let domWit ← mkUniv dPi sol[rV]!
      -- codomain FAMILY: fun (A A' : Type) (aR : domWit.R A A') => ⟨body witness at cPi, with A↦aR⟩
      let pb ← withLocalDeclD `A (.sort (.succ .zero)) fun A =>
        withLocalDeclD `A' (.sort (.succ .zero)) fun A' => do
          let raaTy ← mkAppM ``Param.R #[domWit, A, A']
          withLocalDeclD `aR raaTy fun aR => do
            mkLambdaFVars #[A, A', aR] (← assemble atoms consts sol ((rV, aR) :: env) termEnv cPi body)
      mkAppM ``paramForall #[classToExpr req.1, classToExpr req.2, domWit, pb]
  | .piBase _ bId base body => do
      -- `∀ (x : Base), …` over a registered base: `paramForall` with the base witness as the domain;
      -- the bound term variable `(x, x', xR)` is threaded into `termEnv` for the body's `app` nodes.
      let (dPi, cPi) := depPi req
      let some (baseB, baseWit, baseReg) := atoms.find? base | throwError "assemble: base {base} not registered"
      let domWit ← weakenTo dPi baseReg baseWit
      let pb ← withLocalDeclD `x (mkConst base) fun x =>
        withLocalDeclD `x' baseB fun x' => do
          let xRTy ← mkAppM ``Param.R #[domWit, x, x']
          withLocalDeclD `xR xRTy fun xR => do
            mkLambdaFVars #[x, x', xR]
              (← assemble atoms consts sol env ((bId, (x, x', xR)) :: termEnv) cPi body)
      mkAppM ``paramForall #[classToExpr req.1, classToExpr req.2, domWit, pb]
  | .app _ head bids => do
      -- the abstraction-theorem rule: `⟦head x₁ … xₙ⟧ = ⟦head⟧ x₁ x₁' x₁R … xₙ xₙ' xₙR`, weakened to `req`.
      let some (relator, relClass) := consts.find? head | throwError "assemble: constant {head} not registered"
      let mut argExprs : Array Expr := #[]
      for bId in bids do
        let some (_, x, x', xR) := termEnv.find? (·.1 == bId)
          | throwError "assemble: bound term variable ({bId}) not in scope"
        argExprs := argExprs ++ #[x, x', xR]
      weakenTo req relClass (mkAppN relator argExprs)

/-- full pipeline: solve for minimal classes, then assemble the witness DIRECTLY at `root` — every node
    built by the graded combinator at the class the `dep*` tables dictate (parts never over-provisioned). -/
def transfer (e : Expr) (root : ParamClass) : MetaM (Expr × Shape × Array ParamClass) := do
  let (shape, sol) ← runSolve e root
  let wit ← assemble (← buildAtoms) (← buildConsts) sol [] [] root shape
  return (← instantiateMVars wit, shape, sol)

end Trocq.Solver
