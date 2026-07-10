/-
Prop-in-arrow support: a non-dependent arrow / Π whose DOMAIN or CODOMAIN is a proposition.
  • Tier 1 — `A → Prop` (Type domain, Prop codomain): stays in `paramArrow` (codomain now `Sort uB`).
  • Tier 2 — `P → Q`, `P → A`, `∀ h : P, B h` (Prop domain): routes to `paramForallProp`.
The predicates `Q`/`Q'` are made deliberately NON-defeq (Unary-equality vs Nat-equality) so the whole-diagonal
short-circuit does not fire and the arrow/forall combinators are actually exercised.
-/
import LeTrocq
import Examples.NatUnary
namespace LeTrocq.Tests
open LeTrocq MapClass LeTrocq.Examples

theorem Unary.toNat_eq_zero : ∀ (u : Unary), u.toNat = 0 → u = Unary.z
  | .z,   _ => rfl
  | .s _, _ => by simp [Unary.toNat] at *

def Q  (u : Unary) : Prop := u = Unary.z
def Q' (n : Nat)   : Prop := n = 0
@[trocq] def QR (mc nc : MapClass) (u : Unary) (n : Nat) (uR : RNsym.R u n) :
    Param mc nc (Q u) (Q' n) :=
  paramPropFromMaps mc nc
    (fun h => by unfold Q'; subst h; exact uR.down.symm)
    (fun h => by unfold Q; have := uR.down; rw [h] at this; exact Unary.toNat_eq_zero u this)

/- ===================== Tier 2: Prop DOMAIN (`P → Q`, the former failing case) ===================== -/
def implWit : Param map4 map4 (Q (Unary.s Unary.z) → Q (Unary.s Unary.z))
                              (Q' (Nat.succ 0)   → Q' (Nat.succ 0)) :=
  transfer from (Q (Unary.s Unary.z) → Q (Unary.s Unary.z))
-- the forward transport carries a Unary-side implication to a Nat-side implication:
example (f : Q (Unary.s Unary.z) → Q (Unary.s Unary.z)) : Q' (Nat.succ 0) → Q' (Nat.succ 0) :=
  implWit.cov.map f

/- ===================== Tier 2: Prop DOMAIN, Type codomain (whole arrow is a Type) ===================== -/
example : Param map4 map4 (Q Unary.z → Unary) (Q' 0 → Nat) := transfer from (Q Unary.z → Unary)

/- ===================== Tier 2: dependent Prop domain ===================== -/
example : Param map4 map4 (∀ (_ : Q Unary.z), Unary) (∀ (_ : Q' 0), Nat) :=
  transfer from (∀ (_ : Q Unary.z), Unary)

/- ===================== Tier 1: Type domain, Prop codomain (stays in `paramArrow`) ===================== -/
example : Param map4 map4 (Unary → Q (Unary.s Unary.z)) (Nat → Q' (Nat.succ 0)) :=
  transfer from (Unary → Q (Unary.s Unary.z))

/- ===================== `trocq`: prove a `Prop → Prop` goal on the Unary side via the Nat side ===================== -/
example : Q (Unary.s Unary.z) → Q (Unary.s Unary.z) := by trocq; intro h; exact h
example : Q Unary.z → Q Unary.z := by trocq; intro h; exact h

end LeTrocq.Tests
