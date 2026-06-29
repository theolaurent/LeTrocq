/-
THE DRIVER: solver-directed witness assembly. Two passes over a type `Expr`.

  FRONT HALF (`gen` + `runSolve`):
    walk the type, assign a class `Var` to every node, emit the `Cstr` edges
    (`depArrow`/`depPi`/`depType`/`gev` from `Lattice`), seed the root, and run `LeTrocq.solve`.
    Output: the MINIMAL class each occurrence needs. Reproduces the paper's `∀A:Type, A→A`
    inference *from the actual Expr* (domain `Type` → (2a,0), bound `A` → (1,1)).

  BACK HALF (`assemble`):
    rebuild the witness by dispatching each node to its graded combinator (`paramArrow`, `paramForall`,
    the universe combinator), asking each part only at the `dep*`-minimal class it needs, and weakening
    the registered base leaves to fit. Handles arrows, polymorphic `∀ A : Type`, dependent Π over a
    registered base, and the generic application node (the abstraction theorem
    `⟦head a₁ … aₙ⟧ = ⟦head⟧ a₁ a₁' a₁R … aₙ aₙ' aₙR`, for a relator `head` applied to ARBITRARY argument
    terms — each `aᵢ`'s counterpart `aᵢ'` and relatedness `aᵢR` come from the native term translation).

The registered bases / relators come from the `@[trocq]` extension (`buildAtoms`/`buildConsts`).
-/
import LeTrocq.Core
import LeTrocq.Attr
import LeTrocq.Translate
import Lean
open Lean Lean.Meta
namespace LeTrocq.Solver
open LeTrocq MapClass

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
  | piTerm (v bId : Nat) (dom : Shape) (body : Shape)    -- `∀ (x : T), …` over any buildable domain `T`
  | app    (v : Nat) (head : Name)                       -- `head arg₁ … argₙ`, registered relator `head`
           (argClosures : Array Expr)                    -- every arg abstracted over the in-scope binders
           (typeArgShapes : List (Option Nat × Shape))   -- a sub-shape per TYPE/FAMILY arg (in arg order);
                                                          --   `none` = a type arg, `some bid` = a family arg
                                                          --   whose body is built under element binder `bid`
           (scopeBids : List Nat)                        -- the in-scope binder ids (abstraction order)

def Shape.var : Shape → Nat
  | .atom v _ | .arrow v _ _ | .pi v _ _ _ | .sort v _ | .usevar v _ | .piTerm v _ _ _ | .app v _ _ _ _ => v

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
              st.modify fun s => { s with termBinders := (x.fvarId!, bId) :: s.termBinders }
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
      -- relator's. FAMILY arg `B : X → Type`: introduce an element `a : X` as a (local) TERM binder and gen
      -- the body `B a`; the element is abstracted away inside the sub-shape, so `termBinders` is restored.
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
            let saved := (← st.get).termBinders
            let sub ← withLocalDeclD `a famDom fun a => do
              st.modify fun s => { s with termBinders := (a.fvarId!, elemBid) :: s.termBinders }
              gen atoms consts st (args[i]!.beta #[a])
            st.modify fun s => { s with termBinders := saved }
            emit (.ge sub.var cls)
            tyArgs := tyArgs.push (some elemBid, sub)
        | .term => pure ()
      -- abstract each argument over ALL in-scope binders (base + type); assemble re-instantiates with its own
      -- fvars, then builds each argument's triple — TERM args from the native term translation, TYPE/FAMILY
      -- args from their sub-shape — so arguments may be ANY term: nested apps, λ, families, refs to binders.
      let scope := (← st.get).termBinders ++ (← st.get).binders
      let scopeFvars := (scope.map (fun b => Expr.fvar b.1)).toArray
      let argClosures := args.map (·.abstract scopeFvars)
      let v ← fresh; return .app v head argClosures tyArgs.toList (scope.map (·.2))
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
    if let .base hA hB tyA tyB witName cls := e then
      let wit ← mkConstWithFreshMVarLevels witName
      m ← insertBidir m hA (some hB) (tyB, wit, cls)
        (return (tyA, ← mkAppM ``Param.sym #[wit], (cls.2, cls.1)))
  return m

/-- constant registry from every `@[trocq]` RELATOR (keyed by the applied head, as written). Includes the
    prelude `Quot` relator (`LeTrocq.Std.paramQuotR`), which registers like any other — not a built-in. -/
def buildConsts : MetaM (NameMap (Expr × ParamClass)) := do
  let mut m := mkNameMap _
  for e in trocqEntries (← getEnv) do
    if let .relator hA witName cls := e then m := m.insert hA (← mkConstWithFreshMVarLevels witName, cls)
  return m

/-- run the front half (build registries, generate constraints, solve): shape + minimal class per `Var`. -/
def runSolve (e : Expr) (root : ParamClass) : MetaM (Shape × Array ParamClass) := do
  let st ← IO.mkRef {}
  let shape ← gen (← buildAtoms) (← buildConsts) st e
  let s ← st.get
  return (shape, LeTrocq.solve s.next [(shape.var, root)] s.cstrs.toList)

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
    `env` maps a Π-binder's class var to its bound type variable's `(A, A', aR)` (source/target type +
    relatedness `aR : Param sol[rV] A A'`); `termEnv` does the same for base binders; `sol` supplies each
    binder's solved class. -/
partial def assemble (atoms : NameMap (Expr × Expr × ParamClass)) (consts : NameMap (Expr × ParamClass))
    (sol : Array ParamClass) (env : List (Nat × (Expr × Expr × Expr)))
    (termEnv : List (Nat × (Expr × Expr × Expr))) (req : ParamClass) : Shape → MetaM Expr
  | .atom _ name => do
      let some (_, wit, reg) := atoms.find? name | throwError "assemble: atom {name} not registered"
      weakenTo req reg wit
  | .usevar _ rV => do
      let some (_, _, _, aR) := env.find? (·.1 == rV)
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
            mkLambdaFVars #[A, A', aR] (← assemble atoms consts sol ((rV, (A, A', aR)) :: env) termEnv cPi body)
      mkAppM ``paramForall #[classToExpr req.1, classToExpr req.2, domWit, pb]
  | .piTerm _ bId domShape body => do
      -- `∀ (x : T), …` over any domain `T`: build `T`'s witness by recursively assembling its sub-shape at
      -- the `depPi`-minimal domain class, read the two sides `T`/`T'` off the witness's `Param` type (`whnf`
      -- first — a weaken-free witness can carry a projection rather than a bare `Param … T T'`), then feed it
      -- to `paramForall`. The bound term variable `(x, x', xR)` is threaded into `termEnv` for the body.
      let (dPi, cPi) := depPi req
      let domWit ← assemble atoms consts sol env termEnv dPi domShape
      let domTy := (← whnf (← instantiateMVars (← inferType domWit))).getAppArgs
      let pb ← withLocalDeclD `x domTy[2]! fun x =>
        withLocalDeclD `x' domTy[3]! fun x' => do
          let xRTy ← mkAppM ``Param.R #[domWit, x, x']
          withLocalDeclD `xR xRTy fun xR => do
            mkLambdaFVars #[x, x', xR]
              (← assemble atoms consts sol env ((bId, (x, x', xR)) :: termEnv) cPi body)
      mkAppM ``paramForall #[classToExpr req.1, classToExpr req.2, domWit, pb]
  | .app _ head argClosures typeArgShapes scopeKeys => do
      -- the abstraction theorem `⟦head a₁ … aₙ⟧ = ⟦head⟧ a₁ a₁' a₁R … aₙ aₙ' aₙR`. Each argument `aᵢ` is an
      -- ARBITRARY term: a TERM arg's `(aᵢ', aᵢR)` come from the native term translation (`Translate`, in the
      -- goal→counterpart direction baked into `buildCtx`); a TYPE arg's `(Aᵢ', ARᵢ)` are built by recursively
      -- assembling its sub-shape; a FAMILY arg `B`'s relatedness is the `Param` FAMILY
      -- `fun a a' aR => ⟨witness of B a ≃ B' a'⟩` (built like `paramForall`'s codomain, but the binder is an
      -- ELEMENT related at the preceding type arg's witness). The whole application is then weakened to `req`.
      let some (relator, relClass) := consts.find? head | throwError "assemble: constant {head} not registered"
      let kinds ← relatorArgKinds relator
      -- resolve each in-scope binder to (its source fvar, its translation-`env` entry).
      let resolve (k : Nat) : MetaM (Expr × (FVarId × Expr × Expr)) := do
        match termEnv.find? (·.1 == k) with
        | some (_, x, x', xR) => return (x, (x.fvarId!, x', xR))
        | none => match env.find? (·.1 == k) with
          -- a TYPE binder: pass its parametricity relation `Param.R aR`.
          | some (_, A, A', aR) => return (A, (A.fvarId!, A', ← mkAppM ``Param.R #[aR]))
          | none => throwError "assemble: binder {k} not in scope"
      let resolved ← scopeKeys.mapM resolve
      let asmFvarsArr := (resolved.map (·.1)).toArray
      let transEnv : LeTrocq.Translate.Env := resolved.map (·.2)
      let ctx ← LeTrocq.Translate.buildCtx
      let args := argClosures.map (·.instantiateRev asmFvarsArr)
      let mut tyArgs := typeArgShapes            -- (Option Nat × Shape), consumed left-to-right per TYPE/FAMILY arg
      let mut argExprs : Array Expr := #[]
      let mut argWits : Array (Option Expr) := Array.replicate args.size none  -- each TYPE arg's witness, by index
      for i in [0 : args.size] do
        let arg := args[i]!
        match kinds[i]! with
        | .type cls =>                                     -- TYPE arg: build its `Param` from the sub-shape
            let (_, sub) :: rest := tyArgs
              | throwError "assemble: missing sub-shape for type argument {i} of {head}"
            tyArgs := rest
            let tR ← assemble atoms consts sol env termEnv cls sub
            -- the B-side type is `tR`'s type's 4th arg; `whnf` first, since a weaken-free witness can still
            -- carry the universe combinator's `domWit.R A A'` (a projection) rather than a bare `Param … A A'`.
            let tgt := (← whnf (← instantiateMVars (← inferType tR))).getAppArgs[3]!
            argExprs := argExprs ++ #[arg, tgt, tR]
            argWits := argWits.set! i (some tR)
        | .family cls domIdx =>                            -- FAMILY arg: build the `Param` family + its B-side
            let (some elemBid, sub) :: rest := tyArgs
              | throwError "assemble: missing family sub-shape for argument {i} of {head}"
            tyArgs := rest
            -- the family's domain witness is the TYPE argument named in its binder type (`domIdx`).
            let some paWit := argWits[domIdx]!
              | throwError "assemble: family argument {i} of {head} has no domain type argument (#{domIdx})"
            let paTy := (← whnf (← instantiateMVars (← inferType paWit))).getAppArgs
            let (famB', pbWit) ← withLocalDeclD `a paTy[2]! fun a => withLocalDeclD `a' paTy[3]! fun a' => do
              let aRTy ← mkAppM ``Param.R #[paWit, a, a']
              withLocalDeclD `aR aRTy fun aR => do
                let bodyWit ← assemble atoms consts sol env ((elemBid, (a, a', aR)) :: termEnv) cls sub
                -- the B-side family `B' : A' → Type` is the body witness's B-side; it must depend only on `a'`
                -- (the parametricity B-side), never on the A-side element `a` or the proof `aR`.
                let bside := (← whnf (← instantiateMVars (← inferType bodyWit))).getAppArgs[3]!
                if bside.hasAnyFVar (fun id => id == a.fvarId! || id == aR.fvarId!) then
                  throwError "assemble: family B-side depends on the element/proof — unsupported dependent family in {head}"
                return (← mkLambdaFVars #[a'] bside, ← mkLambdaFVars #[a, a', aR] bodyWit)
            argExprs := argExprs ++ #[arg, famB', pbWit]
        | .term =>                                         -- TERM arg: native counterpart + relatedness
            let (a', aR) ← LeTrocq.Translate.param ctx transEnv arg
            argExprs := argExprs ++ #[arg, a', aR]
      weakenTo req relClass (mkAppN relator argExprs)

/-- full pipeline: solve for minimal classes, then assemble the witness DIRECTLY at `root` — every node
    built by the graded combinator at the class the `dep*` tables dictate (parts never over-provisioned). -/
partial def transfer (e : Expr) (root : ParamClass) : MetaM (Expr × Shape × Array ParamClass) := do
  let (shape, sol) ← runSolve e root
  let wit ← instantiateMVars (← assemble (← buildAtoms) (← buildConsts) sol [] [] root shape)
  -- default any genuinely-free residual universe mvars (e.g. the universe combinator's relation level, or a
  -- universe-poly registered witness's level) to 0 — they're unconstrained, so any level is sound.
  let st := Lean.collectLevelMVars (Lean.collectLevelMVars {} wit) (← instantiateMVars (← inferType wit))
  for mid in st.result do
    unless (← isLevelMVarAssigned mid) do assignLevelMVar mid levelZero
  return (← instantiateMVars wit, shape, sol)

end LeTrocq.Solver
