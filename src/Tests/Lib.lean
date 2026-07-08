/-
The STANDARD-LIBRARY registrations, exercised WITHOUT a user base in scope.

This module imports only `LeTrocq` (not `Examples/NatUnary`), so NO ground-type equivalence is in scope.
With none registered, a ground type transfers to ITSELF via the whole-diagonal short-circuit in `Transfer`
(the generic `paramRefl`, relation `PLift (a = b)`, identity maps) — there is no `Nat ≃ Nat` registration.
A user base like `Nat ≃ Unary` (present in the other test modules) overrides that diagonal whenever it
applies. So these checks pin down the default: `Nat`/`Bool`/`Empty`/`Unit` cross to themselves, and a
composite over only-diagonal parts (`Prod`/`Sum`/`Array`/`List` of `Nat`/`Bool`) is itself diagonal, so it
short-circuits as a whole.
-/
import LeTrocq
namespace LeTrocq.Tests.Lib
open LeTrocq MapClass LeTrocq.Counterpart LeTrocq.Lib

/- DIAGONAL `Nat`: with no equivalence registered, `Nat` transfers to itself. A numeral expands to
   `Nat.succ`/`Nat.zero`; those heads are unregistered, so `⟨·⟩` leaves each as itself (the diagonal). -/
example : (translate (fun n : Nat => Nat.succ (Nat.succ n))) = (fun n : Nat => Nat.succ (Nat.succ n)) := rfl
example : (translate (2 : Nat)) = (2 : Nat) := rfl
/- the relatedness is the generic diagonal `PLift (a = b)` (the whole-diagonal short-circuit's reflexivity). -/
example : PLift ((2 : Nat) = 2) := relate (2 : Nat)
/- and the solver path: `transfer from (Nat → Nat)` is diagonal (both sides cross to themselves), so it is the
   generic `paramRefl` and its forward map is the identity — `(· + 1)` transported is `(· + 1)` itself. -/
example : (transfer from (Nat → Nat)).cov.map (· + 1) 0 = 1 := rfl

/- `Bool` is diagonal in BOTH environments (no `Bool` equivalence is ever registered). Its constructors
   `true`/`false` are unregistered, so `⟨·⟩` crosses them by the diagonal; a `Bool → Bool` function transports
   through the generic `paramRefl` (identity map), `!` and all — no `Bool.rec`/eliminator registration needed. -/
example : (translate (true, false)) = (true, false) := rfl
example : PLift (false = false) := relate false
example : (transfer from (Bool → Bool)).cov.map (fun b => !b) false = true := rfl

/- composites over only-diagonal parts: `Nat × Bool`, `Nat ⊕ Nat`, `Array Nat` are each diagonal as a WHOLE
   (every part crosses to itself), so `assemble` short-circuits the whole type to `paramRefl` — the per-type
   relators (`paramProd`/`paramSum`/`paramArray`) are exercised elsewhere, with a real base. -/
example : (transfer from (Nat × Bool)).cov.map (3, true) = (3, true) := rfl
example : (transfer from (Nat ⊕ Nat)).cov.map (Sum.inr 2) = (Sum.inr 2 : Nat ⊕ Nat) := rfl
example : (transfer from (Array Nat)).cov.map #[1, 2, 3] = #[1, 2, 3] := rfl
example : (translate (#[1, 2] : Array Nat)) = (#[1, 2] : Array Nat) := rfl

/- the EMPTY and UNIT types, in `Type` (`Empty`/`Unit`) and `Prop` (`False`/`True`): each is an unregistered
   leaf that crosses to itself, so it transfers by the diagonal short-circuit (`paramRefl`, at `(4,4)`).
   `Empty`/`Unit` are `Type` (testable via a `Type` former or a value); `True`/`False` are `Prop` and can't
   sit under a `Type` former, so we confirm they assemble directly. -/
example : (transfer from (List Unit)).cov.map [Unit.unit, Unit.unit] = [Unit.unit, Unit.unit] := rfl
example : (transfer from (Option Empty)).cov.map none = none := rfl
example : (transfer from True).cov.map True.intro = True.intro := rfl
noncomputable example : Param map4 map4 False False := transfer from False
noncomputable example : Param map4 map4 Empty Empty := transfer from Empty

/- CONNECTIVE VARIANCE: a `Prop` part is capped at `meet · map1` — `(0,0) ↦ (0,0)`, `(4,4) ↦ (1,1)`,
   `(2a,0) ↦ (1,0)` — since a proposition carries no data above class 1 (completeness free). NOT identity. -/
example : propVariance (map0, map0)  = (map0, map0) := rfl
example : propVariance (map4, map4)  = (map1, map1) := rfl
example : propVariance (map2a, map0) = (map1, map0) := rfl
example : propVariance (map0, map3)  = (map0, map1) := rfl
example : notVariance  (map1, map0)  = (map0, map1) := rfl   -- contravariant: mirror
example : iffVariance  (map1, map0)  = (map1, map1) := rfl   -- both directions ⇒ part is (1,1)

/- EQ VARIANCE: the underlying type is needed only up to COMPLETENESS (`rInMap`, 2b) in each demanded
   direction — never a full `(4,4)` equivalence. A one-directional transport (the `trocq` goal seed `(0,1)`)
   needs only `(0,2b)`; the two-directional maximum is `(2b,2b)`. -/
example : eqVariance (map0, map0) = (map0,  map0)  := rfl
example : eqVariance (map0, map1) = (map0,  map2b) := rfl   -- `trocq` seed: backward completeness only
example : eqVariance (map1, map0) = (map2b, map0)  := rfl   -- forward completeness only
example : eqVariance (map4, map4) = (map2b, map2b) := rfl   -- both directions: the maximum, NOT (4,4)

end LeTrocq.Tests.Lib
