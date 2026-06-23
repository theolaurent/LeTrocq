/- The user surface: the `transfer%` term elaborator and the `trocq` tactic. -/
import Lean
import Trocq.Tactic
import Examples.NatUnary
namespace Trocq.Tests
open Trocq MapClass Trocq.Examples

/- `transfer%` exposes the relatedness witness; its forward map is native function transport over the
   registered `Nat ≃ Unary` base — and it COMPUTES: -/
example : (transfer% (Nat → Nat)).cov.map (· + 1) Unary.z = Unary.s Unary.z := rfl
example : (transfer% (Nat → Nat)).cov.map (fun n => n + 2) Unary.z = Unary.s (Unary.s Unary.z) := rfl
/- the witness relates the two function types by the respectful relation of the base: -/
example : (transfer% (Nat → Nat)).R = RArrow RN.R RN.R := rfl
/- a nested arrow transports too: -/
example : (transfer% (Nat → Nat → Nat)).cov.map (· + ·) Unary.z (Unary.s Unary.z) = Unary.s Unary.z := rfl

/- `trocq` proves a `Unary`-side goal by transferring it to the (easier) `Nat`-side counterpart. -/
example : Unary → Unary := by
  trocq          -- ⊢ Nat → Nat
  exact (· + 1)
example : Unary → Unary → Unary := by
  trocq          -- ⊢ Nat → Nat → Nat
  exact (· + ·)

/- the PAYOFF: a `Prop`-valued dependent goal. `trocq` recognizes `∀ (x : Base), Pred x` via the generic
   `app` rule (registered constant `Pos`), transfers it to the `Nat`-side, and leaves the easier goal. -/
example : ∀ u : Unary, Pos u := by
  trocq                       -- ⊢ ∀ n : Nat, Pos' n
  exact fun n => Nat.zero_le n

/- NO HARDCODING: a predicate registered with `@[trocq]` RIGHT HERE (not in the library) is picked up by
   `trocq` automatically — the driver reads its registries from the `@[trocq]` env extension. -/
def Triv  (u : Unary) : Prop := u = u
def Triv' (n : Nat)   : Prop := n = n
@[trocq] def TrivR (u : Unary) (n : Nat) (_ : RNsym.R u n) : Param map1 map1 (Triv u) (Triv' n) where
  R := fun _ _ => PLift True
  cov    := { map := fun _ => rfl }
  contra := { map := fun _ => rfl }

example : ∀ u : Unary, Triv u := by
  trocq                       -- ⊢ ∀ n : Nat, Triv' n   (resolved via the just-registered `TrivR`)
  exact fun n => rfl

end Trocq.Tests
