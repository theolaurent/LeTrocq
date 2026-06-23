/- Graded dependent-Π family — `paramForall` over the `Nat ≃ Unary` base. -/
import Lean
import Trocq.Combinators.Forall
namespace Trocq.Tests
open Trocq MapClass

/- A constant codomain family exercises the Π plumbing (the relatedness `raa` is still threaded
   through `pb`); the result is the (degenerate-dependent) function space. Forward map at (1,0): -/
def pf10 : Param.{0,0} map1 map0 (∀ _ : Nat, Nat) (∀ _ : Unary, Unary) :=
  paramForall map1 map0 rfl rfl (RN.weaken rfl rfl) (fun _ _ _ => RN.weaken rfl rfl)
example : pf10.cov.down.map Nat.succ Unary.z = Unary.s Unary.z := rfl

/- Section direction at (0,1): the backward map computes. -/
def pf01 : Param.{0,0} map0 map1 (∀ _ : Nat, Nat) (∀ _ : Unary, Unary) :=
  paramForall map0 map1 rfl rfl (RN.weaken rfl rfl) (fun _ _ _ => RN.weaken rfl rfl)
example : pf01.contra.down.map (fun u => u) 5 = 5 := rfl

/- (2b,0): the section combinator carries `R_in_map` (dependent funext), still coherence-free. -/
def pf2b : Param.{0,0} map2b map0 (∀ _ : Nat, Nat) (∀ _ : Unary, Unary) :=
  paramForall map2b map0 rfl rfl (RN.weaken rfl rfl) (fun _ _ _ => RN.weaken rfl rfl)
example : pf2b.cov.down.map Nat.succ Unary.z = Unary.s Unary.z := rfl

/- the combinator is genuinely dependent in its TYPE (B : A → Type); this elaborates the dependent
   codomain `Fin (·+1)` at the type level. -/
example : True := by
  have := @paramForall.{0,0,0,0} Nat Unary (fun n => Fin (n + 1)) (fun u => Fin (toNat u + 1))
  trivial

/-- info: 'Trocq.Tests.pf2b' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms pf2b

end Trocq.Tests
