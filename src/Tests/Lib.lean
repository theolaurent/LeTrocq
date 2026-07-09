/-
Standard-library registrations exercised without a user base in scope (imports only `LeTrocq`).

With no ground-type equivalence registered, a ground type transfers to itself via the whole-diagonal
short-circuit (generic `paramRefl`, relation `PLift (a = b)`, identity maps). These checks pin down that
default: leaves cross to themselves, and a composite over only-diagonal parts is itself diagonal.
-/
import LeTrocq
namespace LeTrocq.Tests.Lib
open LeTrocq MapClass LeTrocq.Counterpart LeTrocq.Lib

/- diagonal `Nat`: with no equivalence registered, `Nat` (and its numerals) transfers to itself. -/
example : (translate (fun n : Nat => Nat.succ (Nat.succ n))) = (fun n : Nat => Nat.succ (Nat.succ n)) := rfl
example : (translate (2 : Nat)) = (2 : Nat) := rfl
/- relatedness is the generic diagonal `PLift (a = b)`. -/
example : PLift ((2 : Nat) = 2) := relate (2 : Nat)
/- solver path: `transfer from (Nat → Nat)` is diagonal, so `paramRefl` with identity forward map. -/
example : (transfer from (Nat → Nat)).cov.map (· + 1) 0 = 1 := rfl

/- `Bool` is always diagonal: constructors and functions cross to themselves via `paramRefl`. -/
example : (translate (true, false)) = (true, false) := rfl
example : PLift (false = false) := relate false
example : (transfer from (Bool → Bool)).cov.map (fun b => !b) false = true := rfl

/- composites over only-diagonal parts are diagonal as a whole, so `assemble` short-circuits to `paramRefl`
   (the per-type relators are exercised elsewhere, with a real base). -/
example : (transfer from (Nat × Bool)).cov.map (3, true) = (3, true) := rfl
example : (transfer from (Nat ⊕ Nat)).cov.map (Sum.inr 2) = (Sum.inr 2 : Nat ⊕ Nat) := rfl
example : (transfer from (Array Nat)).cov.map #[1, 2, 3] = #[1, 2, 3] := rfl
example : (translate (#[1, 2] : Array Nat)) = (#[1, 2] : Array Nat) := rfl

/- empty and unit types in `Type` (`Empty`/`Unit`) and `Prop` (`False`/`True`): each is a diagonal leaf.
   `Type` ones test via a former or value; `Prop` ones assemble directly (can't sit under a `Type` former). -/
example : (transfer from (List Unit)).cov.map [Unit.unit, Unit.unit] = [Unit.unit, Unit.unit] := rfl
example : (transfer from (Option Empty)).cov.map none = none := rfl
example : (transfer from True).cov.map True.intro = True.intro := rfl
noncomputable example : Param map4 map4 False False := transfer from False
noncomputable example : Param map4 map4 Empty Empty := transfer from Empty

/- connective variance: a `Prop` part is capped at `meet · map1` (no data above class 1). Not identity. -/
example : propVariance (map0, map0)  = (map0, map0) := rfl
example : propVariance (map4, map4)  = (map1, map1) := rfl
example : propVariance (map2a, map0) = (map1, map0) := rfl
example : propVariance (map0, map3)  = (map0, map1) := rfl
example : notVariance  (map1, map0)  = (map0, map1) := rfl   -- contravariant: mirror
example : iffVariance  (map1, map0)  = (map1, map1) := rfl   -- both directions ⇒ part is (1,1)

/- eq variance: the type is needed only up to completeness (`rInMap`, 2b) per demanded direction, never a
   full `(4,4)`. The two-directional maximum is `(2b,2b)`. -/
example : eqVariance (map0, map0) = (map0,  map0)  := rfl
example : eqVariance (map0, map1) = (map0,  map2b) := rfl   -- `trocq` seed: backward completeness only
example : eqVariance (map1, map0) = (map2b, map0)  := rfl   -- forward completeness only
example : eqVariance (map4, map4) = (map2b, map2b) := rfl   -- both directions: the maximum, NOT (4,4)

end LeTrocq.Tests.Lib
