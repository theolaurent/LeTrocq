/-
The NATIVE parametricity translation `⟦·⟧`.

Unlike the `Solver` (which builds a graded `Param` *witness* for a TYPE), this is the term-level
abstraction theorem: for any term `t : T` it produces BOTH
  • the native counterpart `t' : T'` (rebuilt over `B` leaf-by-leaf — NOT `iso ∘ t ∘ iso⁻¹`), and
  • the relatedness `tR : ⟦T⟧ t t'`.
It recurses structurally (`.lam`, `.app`, `∀`, sort), bottoms out at registered PRIMITIVES, and unfolds
any other constant's definition. `translate% e` elaborates to the native term `t'`.

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

mutual
/-- translate a TYPE `A` to `(A', R_A)` where `R_A : A → A' → Type` is the parametricity relation. -/
partial def paramType (ctx : Ctx) (env : Env) : Expr → MetaM (Expr × Expr)
  | .const c lvls => do
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
      let (A', relA) ← paramType ctx env A
      if B.hasLooseBVar 0 then
        -- dependent Π: R_{∀x,B} f f' := ∀ x x' (xR : R_A x x'), R_{B x} (f x) (f' x')
        withLocalDeclD n A fun x =>
        withLocalDeclD (n.appendAfter "'") A' fun x' =>
        withLocalDeclD (n.appendAfter "R") (mkApp2 relA x x') fun xR => do
          let (Bx', relBx) ← paramType ctx ((x.fvarId!, x', xR) :: env) (B.instantiate1 x)
          let T' ← mkForallFVars #[x'] Bx'
          let rel ← withLocalDeclD `f e fun f => withLocalDeclD `g T' fun g => do
            let body ← mkForallFVars #[x, x', xR] (mkApp2 relBx (.app f x) (.app g x'))
            mkLambdaFVars #[f, g] body
          return (T', rel)
      else
        -- non-dependent arrow: reuse the library's `RArrow`
        let (B', relB) ← paramType ctx env B
        return (← mkArrow A' B', ← mkAppM ``RArrow #[relA, relB])
  | e => throwError "paramType: unsupported type {e}"

/-- translate a TERM `t : T` to `(t', tR)` where `tR : R_T t t'`. -/
partial def param (ctx : Ctx) (env : Env) : Expr → MetaM (Expr × Expr)
  | .fvar id => do
      match env.find? (·.1 == id) with
      | some (_, x', xR) => return (x', xR)
      | none => throwError "param: unbound variable"
  | .const c lvls => do
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
    | .base hA hB tyA tyB wit _ =>
        types := types.insert hA (tyB, ← mkAppM ``Param.R #[wit])
        types := types.insert hB (tyA, ← mkAppM ``Param.R #[← mkAppM ``Param.sym #[wit]])
    | .term hA bTerm wit =>
        terms := terms.insert hA (bTerm, wit)
        if let some bHead := bTerm.constName? then
          terms := terms.insert bHead (mkConst hA, ← symPrimitive wit)
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
