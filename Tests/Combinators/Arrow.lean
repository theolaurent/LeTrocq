/- The arrow construction: sample combinators + the graded `paramArrow`, over the `Nat ≃ Unary` base. -/
import Lean
import Trocq.Combinators.Arrow
namespace Trocq.Tests
open Trocq MapClass

/- ===================== sample combinators (fixed classes) ===================== -/
def RN33 : Param.{0,0} map3 map3 Nat Unary := RN.weaken (sm := map4) (sn := map4) rfl rfl
def arrowNU : Param.{0,0} map3 map3 (Nat → Nat) (Unary → Unary) := paramArrow33 RN33 RN33
def arrowNU_fun : Param.{0,0} map1 map0 (Nat → Nat) (Unary → Unary) :=
  arrowNU.weaken (sm := map3) (sn := map3) rfl rfl
def RN10 : Param.{0,0} map1 map0 Nat Unary := RN.weaken (sm := map4) (sn := map4) rfl rfl
def RN01 : Param.{0,0} map0 map1 Nat Unary := RN.weaken (sm := map4) (sn := map4) rfl rfl
def arrowNU_low : Param.{0,0} map0 map1 (Nat → Nat) (Unary → Unary) := paramArrowLow RN10 RN01

/- the arrow's induced forward map is native function transport (B.fwd ∘ f ∘ A.bwd); it COMPUTES: -/
example : arrowNU.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl
example : arrowNU.cov.map (fun n => n + 2) Unary.z = Unary.s (Unary.s Unary.z) := rfl
/- weakened to (1,0) ("just the transported function"), still computing: -/
example : arrowNU_fun.cov.down.map Nat.succ Unary.z = Unary.s Unary.z := rfl
/- the minimal-class arrow gives the backward map (here: backward transport of `id`): -/
example : arrowNU_low.contra.down.map (fun u => u) 5 = 5 := rfl
/-- info: 'Trocq.paramArrow33' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms paramArrow33

/- ===================== the graded family at several output classes ===================== -/
def arr01 : Param.{0,0} map0 map1 (Nat → Nat) (Unary → Unary) :=
  paramArrow map0 map1 rfl rfl (RN.weaken rfl rfl) (RN.weaken rfl rfl)
def arr2a : Param.{0,0} map2a map0 (Nat → Nat) (Unary → Unary) :=
  paramArrow map2a map0 rfl rfl (RN.weaken rfl rfl) (RN.weaken rfl rfl)
def arr33 : Param.{0,0} map3 map3 (Nat → Nat) (Unary → Unary) :=
  paramArrow map3 map3 rfl rfl (RN.weaken rfl rfl) (RN.weaken rfl rfl)

example : arr01.contra.down.map (fun u => u) 5 = 5 := rfl                       -- backward, at (0,1)
example : arr2a.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl              -- forward, at (2a,0)
example : arr33.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl              -- forward, at (3,3)
example : arr33.cov.map (fun n => n + 2) Unary.z = Unary.s (Unary.s Unary.z) := rfl
/- soundness survives where the class provides it (2a keeps cov.map_in_R): -/
example : ∀ f f', arr2a.cov.map f = f' → RArrow RN.R RN.R f f' := arr2a.cov.map_in_R
/-- info: 'Trocq.Tests.arr33' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms arr33

end Trocq.Tests
