/-
MILESTONE 4: term-first parametricity-translation driver (fixed class (4,4), no solver yet).

Given a source term `t_A`, the driver `param` traverses it and produces BOTH
  • a native target term `t_B`  (body rebuilt over B leaf-by-leaf — NOT iso-conjugation), and
  • a proof `tR : ⟦T⟧ t_A t_B`  (relatedness).
The class is threaded as a parameter (always (4,4) here) so the §6 solver drops in additively.

Demo: transfer `fun n : Nat => Nat.succ (Nat.succ n)` to a *generated* native `Unary → Unary`
function `fun u => Unary.s (Unary.s u)`, with an axiom-free relatedness proof.
-/
import Lean
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command

/- ===================== the hierarchy + the registered base (from Minimal.lean) ===================== -/
universe u v
namespace Trocq
inductive MapClass | mZero | mOne | mTwoA | mTwoB | mThree | mFour deriving DecidableEq, Repr
abbrev ParamClass := MapClass × MapClass

structure Map0Has {A B : Type u} (_R : A → B → Type v) : Type u where
structure Map1Has {A B : Type u} (_R : A → B → Type v) : Type u where
  map : A → B
structure Map2aHas {A B : Type u} (R : A → B → Type v) where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
structure Map2bHas {A B : Type u} (R : A → B → Type v) : Type u where
  map : A → B
  R_in_map : ∀ a b, R a b → map a = b
structure Map3Has {A B : Type u} (R : A → B → Type v) where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
  R_in_map : ∀ a b, R a b → map a = b
structure Map4Has {A B : Type u} (R : A → B → Type v) where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
  R_in_map : ∀ a b, R a b → map a = b
  R_in_mapK : ∀ a b r, map_in_R a b (R_in_map a b r) = r

def MapHas : MapClass → {A B : Type u} → (A → B → Type v) → Type (max u v)
  | .mZero,  _, _, R => ULift.{v} (Map0Has R)
  | .mOne,   _, _, R => ULift.{v} (Map1Has R)
  | .mTwoA,  _, _, R => Map2aHas R
  | .mTwoB,  _, _, R => ULift.{v} (Map2bHas R)
  | .mThree, _, _, R => Map3Has R
  | .mFour,  _, _, R => Map4Has R

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
  cov :=
    { map := ofNat
      map_in_R := fun n u h => PLift.up (by subst h; exact toNat_ofNat n)
      R_in_map := fun n u r => by have h := r.down; rw [← h, ofNat_toNat]
      R_in_mapK := fun _ _ _ => rfl }
  contra :=
    { map := toNat
      map_in_R := fun u n h => PLift.up h
      R_in_map := fun u n r => r.down
      R_in_mapK := fun _ _ _ => rfl }

/-- registered relatedness for the successor constant: `Nat.succ ~ Unary.s`. -/
def Rsucc (n : Nat) (u : Unary) (h : RNU n u) : RNU (Nat.succ n) (Unary.s u) :=
  PLift.up (by show toNat u + 1 = Nat.succ n; rw [h.down])

/-- the source definition we will transfer. -/
def f : Nat → Nat := fun n => Nat.succ (Nat.succ n)

end Trocq

/- ============================== the driver (metaprogram) ============================== -/
namespace Trocq.Driver
open Trocq

/-- The registration base: type-atoms `c ↦ (B-type, relation)` and term-consts `c ↦ (B-term, witness)`. -/
structure Ctx where
  typeAtoms  : NameMap (Expr × Expr)
  termConsts : NameMap (Expr × Expr)

/-- Relational interpretation of a type: returns `(T_B, relation T_A T_B)`. -/
partial def paramType (ctx : Ctx) (_cls : ParamClass) : Expr → MetaM (Expr × Expr)
  | .const name _ => do
    match ctx.typeAtoms.find? name with
    | some p => return p
    | none   => throwError "paramType: no registered type-relation for {name}"
  | e@(.forallE n A B bi) => do
    if B.hasLooseBVar 0 then throwError "paramType: dependent ∀ unsupported (prototype)"
    let (A', relA) ← paramType ctx _cls A
    let (B', relB) ← paramType ctx _cls (B.instantiate1 (mkConst ``True))
    let T' ← mkArrow A' B'
    withLocalDeclD `fn e fun fn =>
    withLocalDeclD `fn' T' fun fn' => do
      let inner ←
        withLocalDeclD `a A fun a =>
        withLocalDeclD `a' A' fun a' =>
        withLocalDeclD `aR (mkApp2 relA a a') fun aR => do
          mkForallFVars #[a, a', aR] (mkApp2 relB (.app fn a) (.app fn' a'))
      let rel ← mkLambdaFVars #[fn, fn'] inner
      return (T', rel)
  | e => throwError "paramType: unsupported type {e}"

/-- The term translation: `t_A ↦ (t_B, tR : ⟦T⟧ t_A t_B)`. -/
partial def param (ctx : Ctx) (lmap : List (FVarId × Expr × Expr)) (cls : ParamClass) :
    Expr → MetaM (Expr × Expr)
  | .fvar id => do
    match lmap.find? (fun e => e.1 == id) with
    | some (_, x', xR) => return (x', xR)
    | none => throwError "param: unbound fvar {Expr.fvar id}"
  | .const name _ => do
    match ctx.termConsts.find? name with
    | some p => return p
    | none   => throwError "param: no registered transfer for constant {name}"
  | .app fE aE => do
    let (f', fR) ← param ctx lmap cls fE
    let (a', aR) ← param ctx lmap cls aE
    return (.app f' a', mkApp3 fR aE a' aR)
  | .lam n A body _ => do
    let (A', relA) ← paramType ctx cls A
    withLocalDeclD n A fun x => do
      let bodyE := body.instantiate1 x
      withLocalDeclD (n.appendAfter "'") A' fun x' => do
        withLocalDeclD (n.appendAfter "R") (mkApp2 relA x x') fun xR => do
          let lmap' := (x.fvarId!, x', xR) :: lmap
          let (body', bodyR) ← param ctx lmap' cls bodyE
          return (← mkLambdaFVars #[x'] body', ← mkLambdaFVars #[x, x', xR] bodyR)
  | e => throwError "param: unsupported term former {e}"

/-- Build the demo registration base (Nat ≃ Unary). -/
def buildDemoCtx : TermElabM Ctx := do
  let el (s : TSyntax `term) : TermElabM Expr := Term.elabTermAndSynthesize s none
  let unary ← el (← `(Unary))
  let relN  ← el (← `(RN.R))
  let sC    ← el (← `(Unary.s))
  let rsucc ← el (← `(Rsucc))
  return {
    typeAtoms  := (mkNameMap (Expr × Expr)).insert ``Nat (unary, relN)
    termConsts := (mkNameMap (Expr × Expr)).insert ``Nat.succ (sC, rsucc)
  }

end Trocq.Driver

/- ============================== run it: generate f.B and f.R ============================== -/
open Trocq Trocq.Driver in
run_cmd Command.liftTermElabM do
  let srcName : Name := `Trocq.f
  let val := (← getConstInfo srcName).value!
  let ctx ← buildDemoCtx
  let (tB, tR) ← param ctx [] (MapClass.mFour, MapClass.mFour) val
  let tB ← instantiateMVars tB
  let tR ← instantiateMVars tR
  let tBty ← inferType tB
  let tRty ← inferType tR
  addDecl (.defnDecl { name := srcName.str "B", levelParams := [], type := tBty, value := tB,
                       hints := .opaque, safety := .safe })
  addDecl (.defnDecl { name := srcName.str "R", levelParams := [], type := tRty, value := tR,
                       hints := .opaque, safety := .safe })
  logInfo m!"generated  {srcName.str "B"} :=\n  {tB}\n  : {tBty}\n\ngenerated  {srcName.str "R"} :\n  {tRty}"

-- the generated native function and its relatedness proof:
#check (Trocq.f.B : Trocq.Unary → Trocq.Unary)
#print Trocq.f.B
#print axioms Trocq.f.R
