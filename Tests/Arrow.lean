/- Graded arrow family — `paramArrow` at several output classes, over the `Nat ≃ Unary` base. -/
import Lean
import Trocq.Arrow
namespace Trocq.Tests
open Trocq MapClass

/- the same combinator instantiated at three different output classes; each `RN.weaken rfl rfl`
   supplies the part at exactly the `depArrow`-minimal class the combinator asks for. -/
def arr01 : Param.{0,0} map0 map1 (Nat → Nat) (Unary → Unary) :=
  paramArrow map0 map1 rfl rfl (RN.weaken rfl rfl) (RN.weaken rfl rfl)
def arr2a : Param.{0,0} map2a map0 (Nat → Nat) (Unary → Unary) :=
  paramArrow map2a map0 rfl rfl (RN.weaken rfl rfl) (RN.weaken rfl rfl)
def arr33 : Param.{0,0} map3 map3 (Nat → Nat) (Unary → Unary) :=
  paramArrow map3 map3 rfl rfl (RN.weaken rfl rfl) (RN.weaken rfl rfl)

/- every instance produces a witness whose induced maps are native function transport — and COMPUTE: -/
example : arr01.contra.down.map (fun u => u) 5 = 5 := rfl                       -- backward, at (0,1)
example : arr2a.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl              -- forward, at (2a,0)
example : arr33.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl              -- forward, at (3,3)
example : arr33.cov.map (fun n => n + 2) Unary.z = Unary.s (Unary.s Unary.z) := rfl
/- soundness survives where the class provides it (2a keeps cov.map_in_R): -/
example : ∀ f f', arr2a.cov.map f = f' → RArrow RN.R RN.R f f' := arr2a.cov.map_in_R

/- the graded combinator references funext (in its ≥2b arms), so every instance carries Quot.sound
   at the constant level — the proof-free guarantee lives in the separate `paramArrowLow`. -/
/-- info: 'Trocq.Tests.arr33' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms arr33

end Trocq.Tests
