/-
MILESTONE 6, layer 4: WIRE THE DRIVER — solver-directed witness assembly.

Layers 1–3 gave the spine (lattice + solver), the hierarchy + weakening, and the combinators.
Here the metaprogram finally *uses* them end-to-end, replacing the per-shape hardcoding of
`Driver.lean`/`Tactic.lean` (which baked in class (4,4)). Two passes:

  FRONT HALF (the genuinely new integration):
    walk a type `Expr`, assign a class `Var` to every node, emit the Layer-1 `Cstr` edges
    (`depArrow`/`depPi`/`depType`/`gev`), seed the root, and run the real `Trocq.solve`.
    Output: the MINIMAL class each occurrence needs. Reproduces the paper's `∀A:Type, A→A`
    inference *from the actual Expr* (domain `Type` → (2a,0), bound `A` → (1,1)).

  BACK HALF (assembly):
    rebuild the witness by dispatching each former to its combinator (`paramArrow33` for `→`)
    and `weaken`-ing the registered base leaves to fit, then weaken the root to the target class.

Scope: assembly handles arrows over registered base atoms (the non-polymorphic family) and builds
at (3,3) then weakens — enough to drive a real transfer. Consuming the per-node *minimal* classes in
assembly (cheapest combinator per node) + polymorphic binders is what the full graded combinator
family (the deferred 6×6 generalization of layer 3) unlocks; the front half already computes them.
-/
import Trocq.Combinators
import Lean
open Lean Lean.Meta Lean.Elab Lean.Elab.Command
universe u v
namespace Trocq.Solver
open Trocq MapClass

/- ===================== constraint-generation state ===================== -/
structure GenState where
  next    : Nat := 0
  cstrs   : Array Cstr := #[]
  binders : List (FVarId × Nat) := []

/-- shape tree: each node remembers its class `Var`; `usevar` also remembers its binder's class var. -/
inductive Shape
  | atom   (v : Nat) (name : Name)
  | arrow  (v : Nat) (dom cod : Shape)
  | pi     (v domV rV : Nat) (body : Shape)
  | sort   (v rV : Nat)
  | usevar (v rV : Nat)

def Shape.var : Shape → Nat
  | .atom v _ | .arrow v _ _ | .pi v _ _ _ | .sort v _ | .usevar v _ => v

/- ===================== front half: generate constraints from a type Expr ===================== -/
partial def gen (atoms : NameMap (Expr × Expr × ParamClass)) (st : IO.Ref GenState) :
    Expr → MetaM Shape
  | .forallE n A B _ => do
      if B.hasLooseBVar 0 then
        -- dependent Π; only `∀ (x : Type), …` (a type binder) is modelled here
        match A with
        | .sort _ =>
            let v ← fresh; let domV ← fresh; let rV ← fresh
            emit (.depType domV rV)
            withLocalDeclD n A fun x => do
              st.modify fun s => { s with binders := (x.fvarId!, rV) :: s.binders }
              let sb ← gen atoms st (B.instantiate1 x)
              emit (.depPi v domV sb.var)
              return .pi v domV rV sb
        | _ => throwError "gen: dependent Π over non-Type unsupported (prototype)"
      else
        let v ← fresh
        let sd ← gen atoms st A
        let sc ← gen atoms st (B.instantiate1 (mkConst ``True))
        emit (.depArrow v sd.var sc.var)
        return .arrow v sd sc
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

/-- run the front half: returns the shape tree and the solved (minimal) class per `Var`. -/
def runSolve (atoms : NameMap (Expr × Expr × ParamClass)) (e : Expr) (root : ParamClass) :
    MetaM (Shape × Array ParamClass) := do
  let st ← IO.mkRef {}
  let shape ← gen atoms st e
  let s ← st.get
  let sol := Trocq.solve s.next [(shape.var, root)] s.cstrs.toList
  return (shape, sol)

/- ===================== back half: assemble the witness from combinators + weakening ===================== -/
def classToExpr : MapClass → Expr
  | .map0 => mkConst ``MapClass.map0 | .map1 => mkConst ``MapClass.map1
  | .map2a => mkConst ``MapClass.map2a | .map2b => mkConst ``MapClass.map2b
  | .map3 => mkConst ``MapClass.map3 | .map4 => mkConst ``MapClass.map4

/-- `Param.weaken` applied to coerce a witness `p : Param src.1 src.2 _ _` down to `tgt`. -/
def weakenTo (tgt src : ParamClass) (p : Expr) : MetaM Expr := do
  if tgt == src then return p
  let proof (t s : MapClass) : MetaM Expr := do
    mkDecideProof (← mkEq (mkApp2 (mkConst ``MapClass.le) (classToExpr t) (classToExpr s))
                          (mkConst ``Bool.true))
  mkAppM ``Param.weaken #[← proof tgt.1 src.1, ← proof tgt.2 src.2, p]

/-- proof of `MapClass.le t bound = true` (a combinator's class cap), via `decide`. -/
def leProof (t bound : MapClass) : MetaM Expr := do
  mkDecideProof (← mkEq (mkApp2 (mkConst ``MapClass.le) (classToExpr t) (classToExpr bound))
                        (mkConst ``Bool.true))

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
partial def assemble (atoms : NameMap (Expr × Expr × ParamClass)) (sol : Array ParamClass)
    (env : List (Nat × Expr)) (req : ParamClass) : Shape → MetaM Expr
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
          ← assemble atoms sol env da sd, ← assemble atoms sol env dc sc]
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
            mkLambdaFVars #[A, A', aR] (← assemble atoms sol ((rV, aR) :: env) cPi body)
      mkAppM ``paramForall
        #[classToExpr req.1, classToExpr req.2, domWit, pb]

/-- full pipeline: solve for minimal classes, then assemble the witness DIRECTLY at `root` — every node
    built by the graded combinator at the class the `dep*` tables dictate (parts never over-provisioned). -/
def transfer (atoms : NameMap (Expr × Expr × ParamClass)) (e : Expr) (root : ParamClass) :
    MetaM (Expr × Shape × Array ParamClass) := do
  let (shape, sol) ← runSolve atoms e root
  let wit ← assemble atoms sol [] root shape
  return (← instantiateMVars wit, shape, sol)

/- ===================== the registered base + pretty-printer ===================== -/
def demoAtoms : NameMap (Expr × Expr × ParamClass) :=
  (mkNameMap _).insert ``Nat (mkConst ``Unary, mkConst ``RN, (map4, map4))

/-- print the solved class of every named node in the shape tree. -/
partial def report (sol : Array ParamClass) : Shape → MetaM Unit
  | .atom v n      => logInfo m!"  atom {n} : {repr sol[v]!}"
  | .arrow v d c   => do logInfo m!"  → node : {repr sol[v]!}"; report sol d; report sol c
  | .sort v rV     => logInfo m!"  Type : {repr sol[v]!}   (relation-field {repr sol[rV]!})"
  | .pi v dV rV b  => do
      logInfo m!"  ∀ node : {repr sol[v]!}   (domain {repr sol[dV]!}, bound-var class {repr sol[rV]!})"
      report sol b
  | .usevar v _    => logInfo m!"  use : {repr sol[v]!}"

end Trocq.Solver
