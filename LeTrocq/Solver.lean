/-
THE GRADING SOLVER: walk a type `Expr`, infer the MINIMAL class every occurrence needs, and hand back a
`GradedShape` — the shape tree with every node's grade resolved. This is the front half only; it knows
nothing about building witnesses (that is `LeTrocq.Transfer`, the graded translation, which consumes a
`GradedShape` together with the original term).

  walk (`gen`):   assign a class `Var` to every node, emit the `Cstr` edges (`depArrow`/`depPi`/`depType`/
                  `gev`/`ge` from `Lattice`) that relate them, and record a `Shape`.
  solve (`solve`): seed the root, run the monotone least-fixpoint — the minimal class per `Var`.
  bake:           fold the solution into the `Shape`, producing the class-annotated `GradedShape`. The
                  `GradedShape` is fvar-free (binders referenced by a stable id) and term-free (argument
                  terms are read from the ORIGINAL term during translation) — so it is exactly "the result
                  of the solver": grading annotations, nothing more.

`Shape`/`GenState` and the constraint machinery are the solver's INTERNALS; the public product is
`gradeShape : Expr → ParamClass → GradedShape`. The registered bases / relators come from the `@[trocq]`
extension (`buildAtoms`/`buildConsts`).
-/
import LeTrocq.Attr
import Lean
open Lean Lean.Meta
namespace LeTrocq.Solver
open LeTrocq MapClass

/- ===================== per-argument kind of a relator ===================== -/
/-- per-argument kind of a relator, read from its (telescoped) type grouped into abstraction-theorem
    triples `(a, a', aR)` by the SHAPE of the triple's relatedness `aR`:
      • `.type (m,n)`          — `aR : Param m n A A'`                  (a TYPE argument);
      • `.family (m,n) domIdx` — `aR : ∀ a a' (aR : RA a a'), Param m n (B a)(B' a')` (a dependent type
                                 FAMILY, e.g. `Sigma`/`WTree`'s `β`). `domIdx` is the index of the TYPE
                                 argument that is the family's domain `A` — read off `B`'s own binder type,
                                 so the family need NOT sit right after its domain;
      • `.term`                — `aR` a bare relation                  (a TERM argument). -/
inductive ArgKind
  | type   (cls : ParamClass)
  | family (cls : ParamClass) (domIdx : Nat)
  | term
  deriving Inhabited

/- ===================== constraint-generation state + the internal shape tree ===================== -/
structure GenState where
  next    : Nat := 0
  cstrs   : Array Cstr := #[]
  binders : List (FVarId × Nat) := []   -- type-variable binders (`∀ A : Type`) → their relation class var

/-- the solver's internal shape tree: each node remembers its class `Var` (resolved by `solve`, folded in
    by `bake`). Carries no argument terms — those live in the original term the translation re-walks. -/
inductive Shape
  | atom   (v : Nat) (name : Name)
  | arrow  (v : Nat) (dom cod : Shape)
  | pi     (v domV rV : Nat) (body : Shape)              -- `∀ A : Type, …`
  | sort   (v rV : Nat)
  | usevar (v rV : Nat)                                  -- use of a bound TYPE variable (`rV` names the binder)
  | piTerm (v bId : Nat) (dom : Shape) (body : Shape)    -- `∀ (x : T), …` over any buildable domain `T`
  | app    (v : Nat) (head : Name)                       -- `head arg₁ … argₙ`, registered relator `head`
           (kinds : Array ArgKind)                       -- the relator's per-argument kinds (all args)
           (typeArgShapes : List (Option Nat × Shape))   -- a sub-shape per TYPE/FAMILY arg (in arg order);
                                                          --   `none` = a type arg, `some bid` = a family arg
                                                          --   whose body is built under element binder `bid`

def Shape.var : Shape → Nat
  | .atom v _ | .arrow v _ _ | .pi v _ _ _ | .sort v _ | .usevar v _ | .piTerm v _ _ _ | .app v _ _ _ => v

/- ===================== the class-annotated shape (the solver's OUTPUT / the front↔back contract) ===================== -/
/- the grading annotations the translation consumes: the shape with every node's grade RESOLVED. Fvar-free
   (a Π/type binder is named by a stable `bId`, referenced by `usevar`/`piTerm`/`family`) and term-free
   (argument terms are read from the original term). This is all the graded translation needs from the solver. -/
mutual
inductive GradedShape where
  | atom   (cls : ParamClass) (name : Name)
  | arrow  (cls : ParamClass) (dom cod : GradedShape)
  | pi     (cls domCls inner : ParamClass) (bId : Nat) (body : GradedShape)  -- ∀ A:Type; `inner` = bound var's grade
  | sort   (cls inner : ParamClass)
  | usevar (cls : ParamClass) (bId : Nat)                                    -- use of type-var `bId`, at grade `cls`
  | piTerm (cls : ParamClass) (bId : Nat) (dom body : GradedShape)
  | app    (cls : ParamClass) (head : Name) (args : List GradedArg)          -- routing only, no arg terms
/-- one relator argument in a `GradedShape.app`, aligned with the original term's arguments in order. -/
inductive GradedArg where
  | type   (sub : GradedShape)
  | family (elemBid domIdx : Nat) (sub : GradedShape)
  | term
end

instance : Inhabited GradedShape := ⟨.sort default default⟩
instance : Inhabited GradedArg := ⟨.term⟩

def relatorArgKinds (wit : Expr) : MetaM (Array ArgKind) := do
  forallTelescopeReducing (← inferType wit) fun bs _ => do
    let triples ← chunkTriples "relator" wit bs
    let mut kinds : Array ArgKind := #[]
    let mut lastTypeIdx : Nat := 0
    for j in [0 : triples.size] do
      let (aBinder, _, aR) := triples[j]!                 -- `(a, a', aR)`: the A-binder and the relatedness
      let relTy ← inferType aR
      if relTy.getAppFn.isConstOf ``Param then
        let a := relTy.getAppArgs
        kinds := kinds.push (.type (← exprToMapClass a[0]!, ← exprToMapClass a[1]!))
        lastTypeIdx := j
      else
        -- a FAMILY arg's relatedness telescopes to a `Param`; anything else is a bare-relation TERM arg.
        let fam? ← forallTelescopeReducing relTy fun _ concl => do
          if concl.getAppFn.isConstOf ``Param then
            let a := concl.getAppArgs
            return some (← exprToMapClass a[0]!, ← exprToMapClass a[1]!)
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
        | _ =>                                             -- ∀ (x : T), … over ANY buildable domain type `T`
            -- gen the domain `T` to a sub-shape (so the solver builds its `Param`, exactly as for a type
            -- ARGUMENT): a registered base atom, an arrow, a relator application (`List Unary`, …), even a
            -- compound over outer binders. The body's `app` nodes then consume the bound term variable as a
            -- TERM argument whose relatedness is the Π-domain witness — no special base handling needed.
            let v ← fresh; let bId ← fresh
            let sd ← gen atoms consts st A
            withLocalDeclD n A fun x => do
              let sb ← gen atoms consts st (B.instantiate1 x)
              emit (.depPi v sd.var sb.var)
              return .piTerm v bId sd sb
      else
        let v ← fresh
        let sd ← gen atoms consts st A
        let sc ← gen atoms consts st (B.instantiate1 (mkConst ``True))
        emit (.depArrow v sd.var sc.var)
        return .arrow v sd sc
  | e@(.app ..) => do                                     -- `head arg₁ … argₙ`: a registered relator applied
      let some head := e.getAppFn.constName?
        | throwError "gen: application head {e.getAppFn} is not a constant"
      let some (wit, _) := consts.find? head | throwError "gen: unregistered relator {head}"
      let kinds ← relatorArgKinds wit
      let args := e.getAppArgs
      unless args.size == kinds.size do
        throwError "gen: relator {head} takes {kinds.size} arguments but is applied to {args.size}"
      -- TYPE arg: recurse to build its sub-shape (so the solver builds its `Param`), forcing class ≥ the
      -- relator's. FAMILY arg `B : X → Type`: introduce an element `a : X` and gen the body `B a`; the
      -- element is named by `elemBid` (the translation reintroduces it), so nothing leaks into the shape.
      let mut tyArgs : Array (Option Nat × Shape) := #[]
      for i in [0 : args.size] do
        match kinds[i]! with
        | .type cls =>
            let sub ← gen atoms consts st args[i]!
            emit (.ge sub.var cls)
            tyArgs := tyArgs.push (none, sub)
        | .family cls _ =>
            let elemBid ← fresh
            let famDom := (← whnf (← inferType args[i]!)).bindingDomain!
            let sub ← withLocalDeclD `a famDom fun a => gen atoms consts st (args[i]!.beta #[a])
            emit (.ge sub.var cls)
            tyArgs := tyArgs.push (some elemBid, sub)
        | .term => pure ()
      let v ← fresh; return .app v head kinds tyArgs.toList
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

/- ===================== bake: fold the solution into the shape (the annotations) ===================== -/
mutual
/-- fold the solved class assignment `sol` into a `Shape`, resolving every node's `Var` to its `ParamClass`.
    Pure: the grading is fully computed; this just reads it off. -/
partial def bake (sol : Array ParamClass) : Shape → GradedShape
  | .atom v name          => .atom sol[v]! name
  | .arrow v dom cod      => .arrow sol[v]! (bake sol dom) (bake sol cod)
  | .pi v domV rV body    => .pi sol[v]! sol[domV]! sol[rV]! rV (bake sol body)
  | .sort v rV            => .sort sol[v]! sol[rV]!
  | .usevar v rV          => .usevar sol[v]! rV                       -- `bId` = the binder's relation var `rV`
  | .piTerm v bId dom body => .piTerm sol[v]! bId (bake sol dom) (bake sol body)
  | .app v head kinds tyShapes => .app sol[v]! head (bakeArgs sol kinds.toList tyShapes)
/-- align the relator's per-argument kinds with the type/family sub-shapes (term args carry nothing). -/
partial def bakeArgs (sol : Array ParamClass) : List ArgKind → List (Option Nat × Shape) → List GradedArg
  | [], _ => []
  | .term :: ks, ts                       => .term :: bakeArgs sol ks ts
  | .type _ :: ks, (_, sub) :: ts         => .type (bake sol sub) :: bakeArgs sol ks ts
  | .family _ domIdx :: ks, (some eb, sub) :: ts => .family eb domIdx (bake sol sub) :: bakeArgs sol ks ts
  | _ :: ks, ts                           => .term :: bakeArgs sol ks ts   -- unreachable: gen keeps them aligned
end

/- ===================== registries from the `@[trocq]` extension ===================== -/
/-- type-atom registry from every `@[trocq]` BASE, BOTH directions (the base and its `Param.sym`), so a
    type built over either side of an equivalence resolves by head match. -/
def buildAtoms : MetaM (NameMap (Expr × Expr × ParamClass)) := do
  let mut m := mkNameMap _
  for e in trocqEntries (← getEnv) do
    if let .base hA hB tyA tyB witName cls := e then
      let wit ← mkConstWithFreshMVarLevels witName
      m ← insertBidir m hA (some hB) (tyB, wit, cls)
        (return (tyA, ← mkAppM ``Param.sym #[wit], (cls.2, cls.1)))
  return m

/-- constant registry from every `@[trocq]` RELATOR (keyed by the applied head, as written). Includes the
    prelude `Quot` relator (`LeTrocq.ParamLib.paramQuotR`), which registers like any other — not a built-in. -/
def buildConsts : MetaM (NameMap (Expr × ParamClass)) := do
  let mut m := mkNameMap _
  for e in trocqEntries (← getEnv) do
    if let .relator hA witName cls := e then m := m.insert hA (← mkConstWithFreshMVarLevels witName, cls)
  return m

/-- run the front half (build registries, generate constraints, solve): shape + minimal class per `Var`.
    The low-level primitive — exposes the raw `Shape` and solution for inspection/testing. -/
def runSolve (e : Expr) (root : ParamClass) : MetaM (Shape × Array ParamClass) := do
  let st ← IO.mkRef {}
  let shape ← gen (← buildAtoms) (← buildConsts) st e
  let s ← st.get
  return (shape, LeTrocq.solve s.next [(shape.var, root)] s.cstrs.toList)

/-- THE SOLVER'S PRODUCT: infer the minimal class of every occurrence of `e` at output class `root`, and
    return the class-annotated `GradedShape` the graded translation (`LeTrocq.Transfer`) consumes. -/
def gradeShape (e : Expr) (root : ParamClass) : MetaM GradedShape := do
  let (shape, sol) ← runSolve e root
  return bake sol shape

end LeTrocq.Solver
