/-
MILESTONE 4(b): translate a HIGHER-ORDER, DEPENDENTLY-TYPED term — the induction principle.

We translate `nat_ind : ∀ P:Nat→Prop, P 0 → (∀n, P n → P (n+1)) → ∀n, P n` through the parametricity
translation, with `Nat.rec/Nat.zero/Nat.succ` registered as leaves (→ `Unary.rec/.z/.s`). The driver
must now handle: the universe (`Prop`), dependent `Π`, and applied predicates (`P n`). It GENERATES
the clean `Unary` induction principle (its TYPE computed by the type-translation, its TERM by the
term-translation), axiom-free.

SCOPE NOTE: at fixed class (4,4) the recursor-leaf substitution yields the `Unary.rec`-based term;
the *relation-using* deep transfer (proving B-induction from A's recursor via RN, and the slimming
that drops the heavy relational hypotheses) is what the class solver + universe combinator add in
milestone 6 — induction is exactly the example where the lattice earns its keep.
-/
import Lean
open Lean Lean.Meta Lean.Elab Lean.Elab.Command

/- ===================== hierarchy + registered base (Nat ≃ Unary) ===================== -/
universe u v
namespace Trocq
inductive MapClass | mZero | mOne | mTwoA | mTwoB | mThree | mFour deriving DecidableEq, Repr
abbrev ParamClass := MapClass × MapClass

structure Map4Has {A B : Type u} (R : A → B → Type v) where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
  R_in_map : ∀ a b, R a b → map a = b
  R_in_mapK : ∀ a b r, map_in_R a b (R_in_map a b r) = r
def MapHas : MapClass → {A B : Type u} → (A → B → Type v) → Type (max u v)
  | .mFour, _, _, R => Map4Has R
  | _,      _, _, R => ULift.{v} (Map4Has R)   -- (other levels unused in this demo)
structure Param (m n : MapClass) (A B : Type u) where
  R      : A → B → Type v
  cov    : MapHas m R
  contra : MapHas n (fun b a => R a b)

inductive Unary | z | s (n : Unary) deriving Repr
def toNat : Unary → Nat | .z => 0 | .s n => toNat n + 1
def ofNat : Nat → Unary | 0 => .z | n+1 => .s (ofNat n)
theorem toNat_ofNat : ∀ n, toNat (ofNat n) = n
  | 0 => rfl
  | n+1 => by show toNat (ofNat n) + 1 = n + 1; rw [toNat_ofNat n]
theorem ofNat_toNat : ∀ u, ofNat (toNat u) = u
  | .z => rfl
  | .s n => by show Unary.s (ofNat (toNat n)) = Unary.s n; rw [ofNat_toNat n]

def RNU : Nat → Unary → Type := fun n u => PLift (toNat u = n)
def RN : Param.{0,0} .mFour .mFour Nat Unary where
  R := RNU
  cov := { map := ofNat, map_in_R := fun n u h => PLift.up (by subst h; exact toNat_ofNat n),
           R_in_map := fun n u r => by have h := r.down; rw [← h, ofNat_toNat],
           R_in_mapK := fun _ _ _ => rfl }
  contra := { map := toNat, map_in_R := fun u n h => PLift.up h,
              R_in_map := fun u n r => r.down, R_in_mapK := fun _ _ _ => rfl }

/-- registered relatedness witnesses for the leaves. -/
def R0 : RNU Nat.zero Unary.z := PLift.up rfl
def Rsucc (n : Nat) (u : Unary) (h : RNU n u) : RNU (Nat.succ n) (Unary.s u) :=
  PLift.up (by show toNat u + 1 = Nat.succ n; rw [h.down])

/-- the source term to translate: Nat's induction principle (= Nat.rec). -/
def nat_ind : ∀ (P : Nat → Prop), P Nat.zero → (∀ n, P n → P (Nat.succ n)) → ∀ n, P n :=
  fun P h0 hs n => Nat.rec h0 hs n

end Trocq

/- ============================== the driver (mutual param / paramType) ============================== -/
namespace Trocq.Driver
open Trocq

structure Ctx where
  typeAtoms  : NameMap (Expr × Expr)
  termConsts : NameMap (Expr × Expr)
abbrev LMap := List (FVarId × Expr × Expr)

mutual
/-- relational interpretation of a TYPE: `(T_B, ⟦T⟧ : T_A → T_B → Sort _)`. -/
partial def paramType (ctx : Ctx) (lmap : LMap) (cls : ParamClass) : Expr → MetaM (Expr × Expr)
  | .sort lvl => do
      unless lvl == .zero do
        throwError "paramType: only Prop universe supported (Type needs univalence — milestone 6)"
      -- ⟦Prop⟧ p q := p → q → Type   (the type of proof-relations)
      let rel ← withLocalDeclD `p (.sort .zero) fun p =>
        withLocalDeclD `q (.sort .zero) fun q => do
          mkLambdaFVars #[p, q] (← mkArrow p (← mkArrow q (.sort (.succ .zero))))
      return (.sort .zero, rel)
  | .const name _ => do
      match ctx.typeAtoms.find? name with
      | some p => return p
      | none => throwError "paramType: unregistered type constant {name}"
  | .fvar id => do
      match lmap.find? (fun e => e.1 == id) with
      | some (_, x', xR) => return (x', xR)
      | none => throwError "paramType: unbound type fvar"
  | .app h a => do
      let (hT, hR) ← paramType ctx lmap cls h
      let (a', aR) ← param ctx lmap cls a
      return (.app hT a', mkApp3 hR a a' aR)
  | e@(.forallE n A B bi) => do
      let (A', relA) ← paramType ctx lmap cls A
      if !B.hasLooseBVar 0 then
        let (B', relB) ← paramType ctx lmap cls (B.instantiate1 (mkConst ``True))
        let T' ← mkArrow A' B'
        let rel ← withLocalDeclD `f e fun f => withLocalDeclD `g T' fun g => do
          let inner ← withLocalDeclD `a A fun a => withLocalDeclD `a' A' fun a' =>
            withLocalDeclD `aR (mkApp2 relA a a') fun aR =>
              mkForallFVars #[a, a', aR] (mkApp2 relB (.app f a) (.app g a'))
          mkLambdaFVars #[f, g] inner
        return (T', rel)
      else
        withLocalDeclD n A fun x =>
        withLocalDeclD (n.appendAfter "'") A' fun x' =>
        withLocalDeclD (n.appendAfter "R") (mkApp2 relA x x') fun xR => do
          let (Bx', relBx) ← paramType ctx ((x.fvarId!, x', xR) :: lmap) cls (B.instantiate1 x)
          let T' ← mkForallFVars #[x'] Bx'
          let rel ← withLocalDeclD `f e fun f => withLocalDeclD `g T' fun g => do
            mkLambdaFVars #[f, g]
              (← mkForallFVars #[x, x', xR] (mkApp2 relBx (.app f x) (.app g x')))
          return (T', rel)
  | e => throwError "paramType: unsupported type {e}"

/-- term translation: `t_A ↦ (t_B, tR)`. -/
partial def param (ctx : Ctx) (lmap : LMap) (cls : ParamClass) : Expr → MetaM (Expr × Expr)
  | .fvar id => do
      match lmap.find? (fun e => e.1 == id) with
      | some (_, x', xR) => return (x', xR)
      | none => throwError "param: unbound fvar"
  | .const name _ => do
      match ctx.termConsts.find? name with
      | some p => return p
      | none => throwError "param: unregistered constant {name}"
  | .app fE aE => do
      let (f', fR) ← param ctx lmap cls fE
      let (a', aR) ← param ctx lmap cls aE
      return (.app f' a', mkApp3 fR aE a' aR)
  | .lam n A body _ => do
      let (A', relA) ← paramType ctx lmap cls A
      withLocalDeclD n A fun x => withLocalDeclD (n.appendAfter "'") A' fun x' =>
        withLocalDeclD (n.appendAfter "R") (mkApp2 relA x x') fun xR => do
          let (body', bodyR) ← param ctx ((x.fvarId!, x', xR) :: lmap) cls (body.instantiate1 x)
          return (← mkLambdaFVars #[x'] body', ← mkLambdaFVars #[x, x', xR] bodyR)
  | e => throwError "param: unsupported term {e}"
end

def buildCtx : MetaM Ctx := do
  let relNat ← mkAppM ``Param.R #[mkConst ``RN]
  let types := (mkNameMap (Expr × Expr)).insert ``Nat (mkConst ``Unary, relNat)
  -- Unary.rec at universe 0 (the motive lands in Prop)
  let urec := mkConst ``Unary.rec [levelZero]
  let terms := (((mkNameMap (Expr × Expr))
      |>.insert ``Nat.zero (mkConst ``Unary.z, mkConst ``R0))
      |>.insert ``Nat.succ (mkConst ``Unary.s, mkConst ``Rsucc))
      |>.insert ``Nat.rec (urec, urec)
  return { typeAtoms := types, termConsts := terms }

end Trocq.Driver

open Trocq Trocq.Driver in
run_cmd Command.liftTermElabM do
  let val := (← getConstInfo ``Trocq.nat_ind).value!
  let ctx ← buildCtx
  let (tB, _) ← param ctx [] (MapClass.mFour, MapClass.mFour) val
  let tB ← instantiateMVars tB
  let ty ← instantiateMVars (← inferType tB)
  addDecl (.defnDecl { name := `Trocq.uind, levelParams := [], type := ty, value := tB,
                       hints := .opaque, safety := .safe })
  logInfo m!"generated  Trocq.uind :\n  {ty}\n:=\n  {tB}"

open Trocq
#check @Trocq.uind
-- the generated principle is a usable induction principle:
example : ∀ u : Unary, 0 ≤ toNat u :=
  Trocq.uind (fun u => 0 ≤ toNat u) (Nat.le_refl 0) (fun _ ih => Nat.le_succ_of_le ih)
#print axioms Trocq.uind
