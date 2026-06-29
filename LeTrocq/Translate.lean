/-
The NATIVE parametricity translation `⟦·⟧`.

Unlike the `Solver` (which builds a graded `Param` *witness* for a TYPE), this is the term-level
abstraction theorem: for any term `t : T` it produces BOTH
  • the native counterpart `t' : T'` (rebuilt over `B` leaf-by-leaf — NOT `iso ∘ t ∘ iso⁻¹`), and
  • the relatedness `tR : ⟦T⟧ t t'`.
It recurses structurally (`.lam`, `.app`, `∀`, sort), bottoms out at registered PRIMITIVES, and unfolds
any other constant's definition. A **type-valued term** (a recursor's motive `M : Nat → Sort`, or any type
family) is routed through the type-level translation — this is how RECURSORS transport: a recursor is a
registered primitive (`Nat.rec ↦ Unary.rec`) whose motive argument is itself translated. `translate% e`
elaborates to the native term `t'`.

`⟦·⟧` is mutually defined on terms (`param`) and types (`paramType`, which returns the relation `R_T`):
  ⟦c⟧        = registered witness, else ⟦unfold c⟧
  ⟦f a⟧      = (f' a', fR a a' aR)                      -- abstraction theorem
  ⟦fun x=>b⟧ = (fun x'=>b', fun x x' xR => bR)
  ⟦A → B⟧    = (A'→B', RArrow R_A R_B)                  -- as a TYPE: returns the relation
-/
import LeTrocq.ParamCC
import LeTrocq.Attr
import Lean
open Lean Lean.Meta
namespace LeTrocq.Translate

/-- registration: type primitives ↦ (B-type, relation `A→B→Type`); term primitives ↦ (B-term, relatedness);
    PROP primitives (predicates) ↦ (B-predicate, equivalence combinator `… → PLift (p a ↔ p' a')`). -/
structure Ctx where
  types : NameMap (Expr × Expr)
  terms : NameMap (Expr × Expr)
  props : NameMap (Expr × Expr)

/-- bound-variable environment: `fvar ↦ (x', xR)`. `xR` is the relatedness — for a type variable, its
    parametricity relation `x → x' → Type`; for a term/base binder, the bare relatedness. -/
abbrev Env := List (FVarId × Expr × Expr)

/-- recognize a numeral — a raw `.lit (.natVal n)` or an `@OfNat.ofNat _ (lit n) _` — as `n`. The caller
    must additionally check the expression's type is `Nat` (the type argument here may be unreduced). -/
def natNumeral? (e : Expr) : Option Nat :=
  if let some n := e.rawNatLit? then some n
  else if e.getAppFn.isConstOf ``OfNat.ofNat then
    let args := e.getAppArgs
    if args.size == 3 then args[1]!.rawNatLit? else none
  else none

/-- expand `n` to its `Nat.succ`/`Nat.zero` normal form, so a numeral leaf reduces to registered primitives. -/
def natExpr : Nat → Expr
  | 0 => mkConst ``Nat.zero
  | n + 1 => mkApp (mkConst ``Nat.succ) (natExpr n)

/-- re-instantiate a HOMOGENEOUS registration (B-side head = the occurrence head `c` — `List`/`Quot`/`PUnit`
    and their constructors) at the OCCURRENCE's universe levels `lvls`. `Param` relates same-universe types, so
    reusing `lvls` is sound — and it is what lets a UNIVERSE-POLYMORPHIC, content-free primitive like `PUnit`
    get a CONCRETE B-side universe instead of an unpinned fresh one (nothing in the irrelevant `PUnit` would pin
    a fresh mvar, so it would default to the wrong level). `side` is the B-side former/counterpart; `wit` its
    relation/relatedness, re-leveled to `lvls` too when its universe arity matches (the witness is polymorphic
    over the same universes, in order — a monomorphic witness keeps its fixed universes). A heterogeneous entry
    (a BASE `Nat ↦ Unary`, whose two sides are different closed types) is returned unchanged. -/
def relevelHomogeneous (c : Name) (lvls : List Level) (side wit : Expr) : MetaM (Expr × Expr) := do
  unless side.getAppFn.constName? == some c do return (side, wit)
  let wit ← match wit.getAppFn.constName? with
    | some wn => if ((← getConstInfo wn).levelParams).length == lvls.length then pure (.const wn lvls)
                 else pure wit
    | none    => pure wit
  return (.const c lvls, wit)

mutual
/-- translate a TYPE `A` to `(A', R_A)` where `R_A : A → A' → Type` is the parametricity relation. -/
partial def paramType (ctx : Ctx) (env : Env) : Expr → MetaM (Expr × Expr)
  | .const c lvls => do
      -- a registered type former (incl. prelude `Quot`/`PUnit`, see `LeTrocq.ParamLib`), else unfold the definition.
      -- A homogeneous former is re-leveled to the occurrence's universes (`relevelHomogeneous`).
      match ctx.types.find? c with
      | some (B, rel) => relevelHomogeneous c lvls B rel
      | none =>
          let some val := (← getConstInfo c).value? | throwError "paramType: opaque/unregistered type {c}"
          paramType ctx env (val.instantiateLevelParams (← getConstInfo c).levelParams lvls)
  | .fvar id => do
      match env.find? (·.1 == id) with
      | some (_, A', relA) => return (A', relA)
      | none => throwError "paramType: unbound type variable"
  | .app f a => do
      let (f', fR) ← paramType ctx env f
      let (a', aR) ← param ctx env a
      return (.app f' a', mkApp3 fR a a' aR)
  | .sort lvl => do
      -- ⟦Sort u⟧: the B-side is the same sort. The relation between two TYPES is "a relation"
      -- `R_{Type} A A' := A → A' → Type`; the relation between two PROPS is logical equivalence
      -- `R_{Prop} P P' := PLift (P ↔ P')` (matching `paramProp`/the Prop universe), so a `Prop`-valued
      -- component relates by `↔`, not the generic proof-relevant `→ Type`.
      match ← instantiateLevelMVars lvl with
      | .zero =>
          let rel ← withLocalDeclD `P (.sort .zero) fun P => withLocalDeclD `P' (.sort .zero) fun P' => do
            mkLambdaFVars #[P, P'] (← mkAppM ``PLift #[← mkAppM ``Iff #[P, P']])
          return (.sort .zero, rel)
      | lvl =>
          let rel ← withLocalDeclD `A (.sort lvl) fun A => withLocalDeclD `B (.sort lvl) fun B => do
            mkLambdaFVars #[A, B] (← mkArrow A (← mkArrow B (.sort 1)))
          return (.sort lvl, rel)
  | e@(.forallE n A B _) => do
      -- ONE construction for arrow AND dependent Π: R_{∀x,B} f g := ∀ x x' (xR : R_A x x'), R_{B x} (f x)(g x')
      -- (built explicitly, NOT via `RArrow`, so the domain and codomain relations may live at DIFFERENT
      -- universes — needed when the codomain is a `Sort`, e.g. a recursor/matcher motive `Nat → Sort`).
      let (A', relA) ← paramType ctx env A
      withLocalDeclD n A fun x =>
      withLocalDeclD (n.appendAfter "'") A' fun x' =>
      withLocalDeclD (n.appendAfter "R") (mkApp2 relA x x') fun xR => do
        let (Bx', relBx) ← paramType ctx ((x.fvarId!, x', xR) :: env) (B.instantiate1 x)
        let T' ← mkForallFVars #[x'] Bx'
        let rel ← withLocalDeclD `f e fun f => withLocalDeclD `g T' fun g => do
          let body ← mkForallFVars #[x, x', xR] (mkApp2 relBx (.app f x) (.app g x'))
          mkLambdaFVars #[f, g] body
        return (T', rel)
  | e => throwError "paramType: unsupported type {e}"

/-- translate a TERM `t : T` to `(t', tR)` where `tR : R_T t t'`. -/
partial def param (ctx : Ctx) (env : Env) (e : Expr) : MetaM (Expr × Expr) := do
  let ty ← inferType e
  -- a PROPOSITION (`e : Prop`) relates by logical equivalence, via `paramProp`; a (larger) TYPE-valued term
  -- relates by the parametricity *relation*, via `paramType` (this is what lets a recursor's motive
  -- `M : Nat → Sort` or any type-family argument translate). The two meet here.
  if let .sort lvl := ty then
    if (← instantiateLevelMVars lvl) == levelZero then return ← paramProp ctx env e
    else return ← paramType ctx env e
  -- a `Nat` numeral leaf (raw `.lit` or `OfNat.ofNat …`, possibly at an unreduced type like `motive 0`):
  -- expand to its `succ`/`zero` normal form and translate through the registered primitives.
  if let some n := natNumeral? e then
    if (← whnf ty).isConstOf ``Nat then return ← param ctx env (natExpr n)
  match e with
  | .fvar id => do
      match env.find? (·.1 == id) with
      | some (_, x', xR) => return (x', xR)
      | none => throwError "param: unbound variable"
  | .const c lvls => do
      -- a registered term primitive (incl. prelude `Quot.mk`/`PUnit.unit`, see `LeTrocq.ParamLib`), else unfold
      -- the definition. A homogeneous primitive is re-leveled to the occurrence's universes.
      match ctx.terms.find? c with
      | some (bTerm, wit) => relevelHomogeneous c lvls bTerm wit
      | none =>
          let some val := (← getConstInfo c).value? | throwError "param: opaque/unregistered constant {c}"
          param ctx env (val.instantiateLevelParams (← getConstInfo c).levelParams lvls)
  | .app f a => do
      let (f', fR) ← param ctx env f
      let (a', aR) ← param ctx env a
      return (.app f' a', mkApp3 fR a a' aR)
  | .lam n A b _ => do
      let (A', relA) ← paramType ctx env A
      withLocalDeclD n A fun x =>
      withLocalDeclD (n.appendAfter "'") A' fun x' =>
        -- the bound variable's relatedness is `relA x x'`: for a TYPE binder (`A : Sort _`) this is the
        -- parametricity relation `x → x' → Type` (so the body sees the bound type's relation), for a
        -- term/base binder the bare relatedness.
        withLocalDeclD (n.appendAfter "R") (mkApp2 relA x x') fun xR => do
          let (b', bR) ← param ctx ((x.fvarId!, x', xR) :: env) (b.instantiate1 x)
          return (← mkLambdaFVars #[x'] b', ← mkLambdaFVars #[x, x', xR] bR)
  | e => throwError "param: unsupported term {e}"

/-- translate a PROPOSITION `P` to `(P', h)` where `h : PLift (P ↔ P')` — its logical-equivalence relatedness.
    Unlike `∀`-transport (which needs the domain's backward map and so belongs to the solver), an equivalence
    is built from the *relations* alone: logical connectives combine their parts' equivalences congruently, and
    a registered predicate supplies its own (the abstraction theorem `⟦p a₁…⟧ = pR a₁ a₁' a₁R …`). -/
partial def paramProp (ctx : Ctx) (env : Env) (P : Expr) : MetaM (Expr × Expr) := do
  let args := P.getAppArgs
  match P.getAppFn with
  | .const c _ =>
      if (c == ``True || c == ``False) && args.isEmpty then
        return (P, ← mkAppM ``PLift.up #[← mkAppOptM ``Iff.rfl #[P]])
      else if c == ``Not && args.size == 1 then
        let (Q', hQ) ← paramProp ctx env args[0]!
        return (← mkAppM ``Not #[Q'],
          ← mkAppM ``PLift.up #[← mkAppM ``not_congr #[← mkAppM ``PLift.down #[hQ]]])
      else if (c == ``And || c == ``Or || c == ``Iff) && args.size == 2 then
        let (L', hL) ← paramProp ctx env args[0]!
        let (R', hR) ← paramProp ctx env args[1]!
        let cong := if c == ``And then ``and_congr else if c == ``Or then ``or_congr else ``iff_congr
        return (mkApp2 (.const c []) L' R',
          ← mkAppM ``PLift.up #[← mkAppM cong #[← mkAppM ``PLift.down #[hL], ← mkAppM ``PLift.down #[hR]]])
      else match ctx.props.find? c with
        | some (head', wit) =>
            -- the abstraction theorem for a registered predicate `p`: `⟦p a₁ … aₙ⟧ = pR a₁ a₁' a₁R …`.
            let mut cnt := head'
            let mut rel := wit
            for a in args do
              let (a', aR) ← param ctx env a
              cnt := .app cnt a'
              rel := mkApp3 rel a a' aR
            return (cnt, rel)
        | none => throwError "paramProp: unregistered/opaque proposition head {c}"
  | f => throwError "paramProp: unsupported proposition (head {f})"
end

/-- telescope a primitive's type into abstraction-theorem triples `[a,a',aR, b,b',bR, …]`, check the binder
    count is a multiple of 3, and run `k` with the binders `xs` and their VALUE-SWAPPED reordering
    `[a',a,aR, b',b,bR, …]` (the relatedness slot stays put). The shared frame of the backward builders. -/
def withSwappedTriples (what : String) (wit : Expr) (k : Array Expr → Array Expr → MetaM Expr) :
    MetaM Expr := do
  forallTelescope (← inferType wit) fun xs _ => do
    let mut swapped : Array Expr := #[]
    for (a, a', aR) in ← chunkTriples what wit xs do
      swapped := swapped.push a' |>.push a |>.push aR     -- swap the value pair, keep the relatedness
    k xs swapped

/-- swap the (A-value, B-value) in each abstraction-theorem triple of a term primitive, giving the
    BACKWARD-direction combinator. A primitive is `cWit : ∀ a a' (aR : R a a') …, R (c …) (c' …)`
    (binders in triples); this returns `fun a' a aR … => cWit a a' aR …`. Its relatedness binder keeps the
    type `R a a'`, which is *defeq* to the symmetric relation `R.sym a' a` the backward direction supplies —
    so the same proof term serves both directions, only the value arguments swap position. -/
def symPrimitive (wit : Expr) : MetaM Expr :=
  withSwappedTriples "term primitive" wit fun xs swapped => mkLambdaFVars swapped (mkAppN wit xs)

/-- the backward direction of a PROP primitive `pR : ∀ triples, PLift (p … ↔ p' …)`: like `symPrimitive`
    (swap each triple's value pair), but the conclusion is an `Iff`, so the proof is `Iff.symm`'d too. -/
def symProp (wit : Expr) : MetaM Expr :=
  withSwappedTriples "prop primitive" wit fun xs swapped => do
    let pf ← mkAppM ``PLift.up #[← mkAppM ``Iff.symm #[← mkAppM ``PLift.down #[mkAppN wit xs]]]
    mkLambdaFVars swapped pf

/-- the translation context assembled from the `@[trocq]` extension, in BOTH directions: every BASE gives a
    type relation forward (`Param.R`) and backward (`Param.R ∘ Param.sym`); every TERM primitive gives its
    `c ↦ c'` map + relatedness forward, and the swapped `c' ↦ c` map + `symPrimitive` relatedness backward.
    So a term over *either* side of a registered equivalence translates by head match. -/
def buildCtx : MetaM Ctx := do
  let mut types := mkNameMap _
  let mut terms := mkNameMap _
  let mut props := mkNameMap _
  -- every BASE / TERM / PROP primitive installs in both directions via `insertBidir` (the shared
  -- forward/backward + homogeneous-skip policy); the backward witness is the relevant `sym*`.
  for e in trocqEntries (← getEnv) do
    match e with
    | .base hA hB tyA tyB witName _ =>
        let wit ← mkConstWithFreshMVarLevels witName
        types ← insertBidir types hA (some hB) (tyB, ← mkAppM ``Param.R #[wit])
          (return (tyA, ← mkAppM ``Param.R #[← mkAppM ``Param.sym #[wit]]))
    | .term hA bTerm witName =>
        -- the backward key is the B-side head (so a homogeneous constructor like `List.cons` is skipped).
        let wit ← mkConstWithFreshMVarLevels witName
        terms ← insertBidir terms hA bTerm.constName? (bTerm, wit)
          (return (← mkConstWithFreshMVarLevels hA, ← symPrimitive wit))
    | .propPrim hA hB witName =>
        let wit ← mkConstWithFreshMVarLevels witName
        props ← insertBidir props hA (some hB) (← mkConstWithFreshMVarLevels hB, wit)
          (return (← mkConstWithFreshMVarLevels hA, ← symProp wit))
    | .typeFormer hA hB relName =>
        -- a parameterized type former `F`: `paramType` crosses `F a` via `(F', relFormer)`, where
        -- `relFormer a a' aR : F a → F' a' → Type` is applied by the `.app` rule's `mkApp3`. ONE entry
        -- serves BOTH directions (the per-argument relation `aR` carries the direction and `relFormer` is
        -- polymorphic in it), so no `sym` exists to install — forward only.
        types := types.insert hA (← mkConstWithFreshMVarLevels hB, ← mkConstWithFreshMVarLevels relName)
    | .relator .. => pure ()
  return { types, terms, props }

end LeTrocq.Translate
