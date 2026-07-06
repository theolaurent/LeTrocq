/- The arrow construction: the graded `paramArrow` at several output classes, over the `Nat ≃ Unary` base. -/
import Lean
import LeTrocq.Combinators.Arrow
import Examples.NatUnary
namespace LeTrocq.Tests
open LeTrocq MapClass LeTrocq.Examples

/- ===================== the grading table (output class → minimal part classes) ===================== -/
example : arrowVariance (map1, map0) = ((map0,map1), (map1,map0)) := rfl
example : arrowVariance (map0, map1) = ((map1,map0), (map0,map1)) := rfl   -- symmetric
example : arrowVariance (map4, map4) = ((map4,map4),(map4,map4)) := rfl    -- top propagates to both parts

/- ===================== the graded family at several output classes (incl. (4,4)) ===================== -/
def arr01 : Param map0 map1 (Nat → Nat) (Unary → Unary) :=
  paramArrow map0 map1 (RN.weaken rfl rfl) (RN.weaken rfl rfl)
def arr2a : Param map2a map0 (Nat → Nat) (Unary → Unary) :=
  paramArrow map2a map0 (RN.weaken rfl rfl) (RN.weaken rfl rfl)
def arr33 : Param map3 map3 (Nat → Nat) (Unary → Unary) :=
  paramArrow map3 map3 (RN.weaken rfl rfl) (RN.weaken rfl rfl)
def arr44 : Param map4 map4 (Nat → Nat) (Unary → Unary) :=
  paramArrow map4 map4 (RN.weaken rfl rfl) (RN.weaken rfl rfl)

example : arr01.contra.map (fun u => u) 5 = 5 := rfl                       -- backward, at (0,1)
example : arr2a.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl              -- forward, at (2a,0)
example : arr33.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl              -- forward, at (3,3)
example : arr33.cov.map (fun n => n + 2) Unary.z = Unary.s (Unary.s Unary.z) := rfl
/- the (4,4) equivalence is now buildable: forward map computes, and its coherence field exists. -/
example : arr44.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl
example : ∀ f f' r, arr44.cov.map_in_R f f' (arr44.cov.R_in_map f f' r) = r := arr44.cov.R_in_mapK
/- the backward (contra) map is native transport too, and the carried relation is exactly `RArrow`: -/
example : arr44.contra.map (fun u => u) 5 = 5 := rfl
example : arr44.R = RArrow RN.R RN.R := rfl
/- soundness survives where the class provides it (2a keeps cov.map_in_R): -/
example : ∀ f f', arr2a.cov.map f = f' → RArrow RN.R RN.R f f' := arr2a.cov.map_in_R

/- the (2b,0) section: cov is `Map2bHas` (map + completeness), no soundness; forward map computes. -/
def arr2b : Param map2b map0 (Nat → Nat) (Unary → Unary) :=
  paramArrow map2b map0 (RN.weaken rfl rfl) (RN.weaken rfl rfl)
example : arr2b.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl

/-- info: 'LeTrocq.Tests.arr44' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms arr44

end LeTrocq.Tests
