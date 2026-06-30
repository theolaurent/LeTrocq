/-
The STANDARD-LIBRARY registrations, exercised WITHOUT a user base in scope.

This module imports only `LeTrocq` (not `Examples/NatUnary`), so the library's OWN registrations are the
only ones present — in particular `Nat` is the `LeTrocq.ParamLib` DIAGONAL (`Nat ≃ Nat`), not the worked
example's `Nat ≃ Unary` (which shadows it in the other test modules). So these checks pin down the default,
overridable registrations on their own terms: `Nat`/`Bool` cross to themselves, and the parameterized
formers (`Prod`/`Sum`/`Array`/`List`) lift the diagonal componentwise.
-/
import LeTrocq
namespace LeTrocq.Tests.ParamLib
open LeTrocq MapClass LeTrocq.Translate LeTrocq.ParamLib

/- DIAGONAL `Nat`: with no other equivalence registered, `Nat` transfers to itself. The numeral leaf expands
   to `Nat.succ`/`Nat.zero`, which the constructor term primitives (`NatSuccR`/`NatZeroR`) carry. -/
example : (translate% (fun n : Nat => Nat.succ (Nat.succ n))) = (fun n : Nat => Nat.succ (Nat.succ n)) := rfl
example : (translate% (2 : Nat)) = (2 : Nat) := rfl
/- the relatedness is the diagonal `NatR` (built through `NatSuccR`/`NatZeroR`). -/
example : NatR 2 2 := relate% (2 : Nat)
/- and the solver path: `transfer% (Nat → Nat)` is the identity equivalence, so its forward map is the
   function itself — `paramNatR` weakened/threaded through `paramArrow`. -/
example : (transfer% (Nat → Nat)).cov.map (· + 1) 0 = 1 := rfl

/- `Bool` is diagonal in BOTH environments (no other `Bool` equivalence exists). The translation crosses the
   CONSTRUCTORS (`true`/`false`); an ELIMINATOR like `!` (which unfolds to `Bool.rec`) is not registered, just
   as `Quot.lift`/recursors aren't — the solver path still transports a `Bool → Bool` function wholesale. -/
example : (translate% (true, false)) = (true, false) := rfl
example : BoolR false false := relate% false
example : (transfer% (Bool → Bool)).cov.map (fun b => !b) false = true := rfl

/- the parameterized formers over the diagonal: each lifts `Nat ≃ Nat` componentwise, so they too transfer
   to themselves — exercising `paramProdR`/`paramSumR`/`paramArrayR` with a non-`Unary` base. -/
example : (transfer% (Nat × Bool)).cov.map (3, true) = (3, true) := rfl
example : (transfer% (Nat ⊕ Nat)).cov.map (Sum.inr 2) = (Sum.inr 2 : Nat ⊕ Nat) := rfl
example : (transfer% (Array Nat)).cov.map #[1, 2, 3] = #[1, 2, 3] := rfl
example : (translate% (#[1, 2] : Array Nat)) = (#[1, 2] : Array Nat) := rfl

/- the EMPTY and UNIT types, in `Type` (`Empty`/`Unit`) and `Prop` (`False`/`True`): each is a parameter-less
   `(4,4)` base, so it transfers to itself. `Empty`/`Unit` are `Type` leaves (testable via a `Type` former or
   a value); `True`/`False` are `Prop` and can't sit under a `Type` former, so we confirm they assemble. -/
example : (transfer% (List Unit)).cov.map [Unit.unit, Unit.unit] = [Unit.unit, Unit.unit] := rfl
example : (transfer% (Option Empty)).cov.map none = none := rfl
example : (transfer% True).cov.map True.intro = True.intro := rfl
noncomputable example : Param map4 map4 False False := transfer% False
noncomputable example : Param map4 map4 Empty Empty := transfer% Empty

end LeTrocq.Tests.ParamLib
