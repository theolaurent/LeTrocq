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
import Trocq.Combinators
import Trocq.Attr
import Lean
open Lean Lean.Meta
namespace Trocq.Translate

/-- registration: type primitives ↦ (B-type, relation `A→B→Type`); term primitives ↦ (B-term, relatedness). -/
structure Ctx where
  types : NameMap (Expr × Expr)
  terms : NameMap (Expr × Expr)

/-- bound-variable environment: `fvar ↦ (x', xR)` (for a type var, `xR` is its relation). -/
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

mutual
/-- translate a TYPE `A` to `(A', R_A)` where `R_A : A → A' → Type` is the parametricity relation. -/
partial def paramType (ctx : Ctx) (env : Env) : Expr → MetaM (Expr × Expr)
  | .const c lvls => do
      -- `PUnit` (the dummy argument a non-recursive matcher introduces) relates to itself by the trivial
      -- always-inhabited relation `fun _ _ => PUnit` — built in, since it has no `@[trocq]` registration.
      if c == ``PUnit then
        let pu := Expr.const ``PUnit lvls
        let rel ← withLocalDeclD `a pu fun a => withLocalDeclD `b pu fun b =>
          mkLambdaFVars #[a, b] (Expr.const ``PUnit [levelOne])
        return (pu, rel)
      match ctx.types.find? c with
      | some p => return p
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
      -- ⟦Sort u⟧: the B-side is the same sort; the relation between two types is "a relation"
      -- `R_{Sort u} A A' := A → A' → Type` (so a TYPE `A : Sort u` translates to a relation `R_A`).
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
  -- a TYPE-valued term is translated at the type level: its counterpart is the translated type and its
  -- "relatedness" is the parametricity *relation*. This is what lets a recursor's motive `M : Nat → Sort`
  -- (and any type-family argument) translate — the term/type translations meet here.
  if ty.isSort then return ← paramType ctx env e
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
      -- the unique `PUnit.unit` relates to itself; its relatedness inhabits the trivial `PUnit` relation.
      if c == ``PUnit.unit then
        return (Expr.const ``PUnit.unit lvls, Expr.const ``PUnit.unit [levelOne])
      match ctx.terms.find? c with
      | some p => return p
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
      withLocalDeclD (n.appendAfter "R") (mkApp2 relA x x') fun xR => do
        let (b', bR) ← param ctx ((x.fvarId!, x', xR) :: env) (b.instantiate1 x)
        return (← mkLambdaFVars #[x'] b', ← mkLambdaFVars #[x, x', xR] bR)
  | e => throwError "param: unsupported term {e}"
end

/-- swap the (A-value, B-value) in each abstraction-theorem triple of a term primitive, giving the
    BACKWARD-direction combinator. A primitive is `cWit : ∀ a a' (aR : R a a') …, R (c …) (c' …)`
    (binders in triples); this returns `fun a' a aR … => cWit a a' aR …`. Its relatedness binder keeps the
    type `R a a'`, which is *defeq* to the symmetric relation `R.sym a' a` the backward direction supplies —
    so the same proof term serves both directions, only the value arguments swap position. -/
def symPrimitive (wit : Expr) : MetaM Expr := do
  forallTelescope (← inferType wit) fun xs _ => do
    unless xs.size % 3 == 0 do
      throwError "trocq: term primitive is not in abstraction-theorem triple form ({xs.size} binders): {wit}"
    let mut swapped : Array Expr := #[]
    for j in [0 : xs.size / 3] do
      swapped := (swapped.push xs[3*j+1]!).push xs[3*j]! |>.push xs[3*j+2]!
    mkLambdaFVars swapped (mkAppN wit xs)

/-- the translation context assembled from the `@[trocq]` extension, in BOTH directions: every BASE gives a
    type relation forward (`Param.R`) and backward (`Param.R ∘ Param.sym`); every TERM primitive gives its
    `c ↦ c'` map + relatedness forward, and the swapped `c' ↦ c` map + `symPrimitive` relatedness backward.
    So a term over *either* side of a registered equivalence translates by head match. -/
def buildCtx : MetaM Ctx := do
  let mut types := mkNameMap _
  let mut terms := mkNameMap _
  for e in trocqEntries (← getEnv) do
    match e with
    | .base hA hB tyA tyB witName _ =>
        let wit ← mkConstWithFreshMVarLevels witName
        types := types.insert hA (tyB, ← mkAppM ``Param.R #[wit])
        types := types.insert hB (tyA, ← mkAppM ``Param.R #[← mkAppM ``Param.sym #[wit]])
    | .term hA bTerm witName =>
        let wit ← mkConstWithFreshMVarLevels witName
        terms := terms.insert hA (bTerm, wit)
        -- backward map `c' ↦ c`: ONLY for a HETEROGENEOUS primitive (distinct heads, e.g. `Nat.succ ↦
        -- Unary.s`). For a homogeneous one (a polymorphic constructor like `List.cons ↦ List.cons`) the
        -- forward `wit` already serves both directions — it is polymorphic in the element relation, which
        -- carries the direction — and a swapped entry under the SAME head would clobber it (and strip the
        -- constructor's universe levels via the level-free `mkConst`).
        if let some bHead := bTerm.constName? then
          if bHead != hA then
            terms := terms.insert bHead (← mkConstWithFreshMVarLevels hA, ← symPrimitive wit)
    | .typeFormer hA hB relName =>
        -- a parameterized type former `F`: `paramType` crosses `F a` via `(F', relFormer)`, where
        -- `relFormer a a' aR : F a → F' a' → Type` is applied by the `.app` rule's `mkApp3`. ONE entry
        -- serves BOTH directions — the per-argument relation `aR` carries the direction and `relFormer`
        -- is polymorphic in it (for a homogeneous `F`, `hB = hA`, so there is nothing extra to add).
        types := types.insert hA (← mkConstWithFreshMVarLevels hB, ← mkConstWithFreshMVarLevels relName)
    | .relator .. => pure ()
  return { types, terms }

/-- `translate% t` ⤳ the native `B`-side counterpart `t'` (rebuilt over `B`, not iso-conjugation). -/
elab "translate% " t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let (e', _) ← param (← buildCtx) [] (← instantiateMVars e)
  instantiateMVars e'

/-- `relate% t` ⤳ the relatedness `tR : ⟦T⟧ t t'` — the proof the native counterpart is correct. -/
elab "relate% " t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let (_, eR) ← param (← buildCtx) [] (← instantiateMVars e)
  instantiateMVars eR

end Trocq.Translate
