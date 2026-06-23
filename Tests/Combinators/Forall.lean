/- Graded dependent-Π family — `paramForall` over the `Nat ≃ Unary` base, now at every output class. -/
import Lean
import Trocq.Combinators.Forall
namespace Trocq.Tests
open Trocq MapClass

/- A constant codomain family exercises the Π plumbing (the relatedness `raa` is still threaded
   through `pb`); the result is the (degenerate-dependent) function space. Forward map at (1,0): -/
def pf10 : Param.{0,0} map1 map0 (∀ _ : Nat, Nat) (∀ _ : Unary, Unary) :=
  paramForall map1 map0 (RN.weaken rfl rfl) (fun _ _ _ => RN.weaken rfl rfl)
example : pf10.cov.down.map Nat.succ Unary.z = Unary.s Unary.z := rfl

/- Section direction at (0,1): the backward map computes. -/
def pf01 : Param.{0,0} map0 map1 (∀ _ : Nat, Nat) (∀ _ : Unary, Unary) :=
  paramForall map0 map1 (RN.weaken rfl rfl) (fun _ _ _ => RN.weaken rfl rfl)
example : pf01.contra.down.map (fun u => u) 5 = 5 := rfl

/- (3,3): full soundness+completeness — needs the domain at class 4 (RN is) and the `subst`+subsingleton
   transport in `map_in_R`. Forward map still computes. -/
def pf33 : Param.{0,0} map3 map3 (∀ _ : Nat, Nat) (∀ _ : Unary, Unary) :=
  paramForall map3 map3 (RN.weaken rfl rfl) (fun _ _ _ => RN.weaken rfl rfl)
example : pf33.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl

/- (4,4): the full dependent-Π equivalence — past the old 2b cap. The coherence `R_in_mapK` exists. -/
def pf44 : Param.{0,0} map4 map4 (∀ _ : Nat, Nat) (∀ _ : Unary, Unary) :=
  paramForall map4 map4 (RN.weaken rfl rfl) (fun _ _ _ => RN.weaken rfl rfl)
example : pf44.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl
example : ∀ f f' r, pf44.cov.map_in_R f f' (pf44.cov.R_in_map f f' r) = r := pf44.cov.R_in_mapK

/- the combinator is genuinely dependent in its TYPE (B : A → Type); this elaborates the dependent
   codomain `Fin (·+1)` at the type level. -/
example : True := by
  have := @paramForall.{0,0,0,0} Nat Unary (fun n => Fin (n + 1)) (fun u => Fin (toNat u + 1))
  trivial

/-- info: 'Trocq.Tests.pf44' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms pf44

end Trocq.Tests
