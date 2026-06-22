/-
MILESTONE 5(a): the `trocq` TACTIC (goal transfer via comap).

`by trocq` inspects the goal `∀ u : Unary, Q u`, transfers it across the registered `Nat ≃ Unary`
relation to `∀ n : Nat, P n`, and refines the original goal with the implication
`(∀ n, P n) → (∀ u, Q u)` built from RN's backward map + the registered predicate relation.
You are left to prove the (easier) Nat-side goal.

This is the comap direction (Trocq seeds the goal at class (0,1)); here fixed at the (4,4) base.
Scope: single `∀` over the registered base type, body a registered predicate. Generalising the
recursion (nested binders, arrows, the universe) follows the same shape as the term driver; doing it
at *minimal* classes (so the new goal is as weak as possible) is milestone 6.
-/
import Lean
open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

universe u v
namespace Trocq
inductive MapClass | mZero | mOne | mTwoA | mTwoB | mThree | mFour deriving DecidableEq, Repr

structure Map4Has {A B : Type u} (R : A → B → Type v) where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
  R_in_map : ∀ a b, R a b → map a = b
  R_in_mapK : ∀ a b r, map_in_R a b (R_in_map a b r) = r
def MapHas : MapClass → {A B : Type u} → (A → B → Type v) → Type (max u v)
  | .mFour, _, _, R => Map4Has R
  | _,      _, _, R => ULift.{v} (Map4Has R)
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

/-- RN's backward map and "diagonal" witness — the data the comap needs (= RN.contra.map etc.). -/
def RN_comap : Unary → Nat := toNat
def RN_diag (u : Unary) : RNU (RN_comap u) u := PLift.up rfl

/-- a registered predicate relation: `P : Nat → Prop` ~ `Q : Unary → Prop`, with the comap direction. -/
def P (n : Nat) : Prop := 0 ≤ n
def Q (u : Unary) : Prop := 0 ≤ toNat u
def PQ (n : Nat) (u : Unary) (r : RNU n u) (hp : P n) : Q u := by
  show 0 ≤ toNat u; rw [r.down]; exact hp

end Trocq

/- ============================== the tactic ============================== -/
/-- registry: predicate-const ↦ (Nat-side predicate, comap witness). -/
def trocqRegistry : MetaM (NameMap (Expr × Expr)) :=
  return (mkNameMap (Expr × Expr)).insert ``Trocq.Q (mkConst ``Trocq.P, mkConst ``Trocq.PQ)

elab "trocq" : tactic => withMainContext do
  let g ← getMainGoal
  let .forallE _ dom body _ ← g.getType | throwError "trocq: goal is not a ∀"
  unless ← isDefEq dom (mkConst ``Trocq.Unary) do
    throwError "trocq: binder type is not the registered base `Unary`"
  let qName := body.getAppFn.constName!                    -- body = Q (bvar 0)
  let some (pSrc, pqWit) := (← trocqRegistry).find? qName
    | throwError "trocq: predicate {qName} is not registered"
  -- new (Nat-side) goal:  ∀ n : Nat, P n
  let srcType ← withLocalDeclD `n (mkConst ``Nat) fun n => mkForallFVars #[n] (mkApp pSrc n)
  -- implication  (∀ n, P n) → (∀ u, Q u)  built from RN's backward map + the predicate comap:
  let impl ← withLocalDeclD `h srcType fun h =>
    withLocalDeclD `u (mkConst ``Trocq.Unary) fun u => do
      let cu   ← mkAppM ``Trocq.RN_comap #[u]               -- toNat u
      let diag ← mkAppM ``Trocq.RN_diag  #[u]               -- RNU (toNat u) u
      let pq   := mkAppN pqWit #[cu, u, diag, mkApp h cu]   -- PQ (toNat u) u diag (h (toNat u)) : Q u
      mkLambdaFVars #[h, u] pq
  let newGoal ← mkFreshExprMVar srcType
  g.assign (mkApp impl newGoal)
  setGoals [newGoal.mvarId!]

/- ============================== demo ============================== -/
namespace Trocq
-- prove a Unary statement by transferring it to the (easier) Nat statement:
theorem foo : ∀ u : Unary, Q u := by
  trocq                 -- goal becomes  ⊢ ∀ n : Nat, P n
  exact Nat.zero_le     -- discharge the Nat-side goal
#print axioms foo
end Trocq
