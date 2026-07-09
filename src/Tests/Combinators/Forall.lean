/- Graded dependent-Π family — `paramForall` over the `Nat ≃ Unary` base, now at every output class. -/
import Lean
import LeTrocq.Combinators.Forall
import Examples.NatUnary
namespace LeTrocq.Tests
open LeTrocq MapClass LeTrocq.Examples

/- ===================== the grading table (output class → minimal part classes) ===================== -/
example : forallVariance (map1, map0) = ((map0,map2a),(map1,map0)) := rfl
example : forallVariance (map4, map0) = ((map0,map4), (map4,map0)) := rfl
example : forallVariance (map0, map1) = ((map2a,map0),(map0,map1)) := rfl
example : forallVariance (map2a, map0) = ((map0,map4),(map2a,map0)) := rfl   -- Π domain needs the full equivalence

/- constant codomain family exercises the Π plumbing; forward map at (1,0). -/
def pf10 : Param map1 map0 (∀ _ : Nat, Nat) (∀ _ : Unary, Unary) :=
  paramForall map1 map0 (RN.weaken rfl rfl) (fun _ _ _ => RN.weaken rfl rfl)
example : pf10.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl

/- Section direction at (0,1): the backward map computes. -/
def pf01 : Param map0 map1 (∀ _ : Nat, Nat) (∀ _ : Unary, Unary) :=
  paramForall map0 map1 (RN.weaken rfl rfl) (fun _ _ _ => RN.weaken rfl rfl)
example : pf01.contra.map (fun u => u) 5 = 5 := rfl

/- (2a,0): soundness via the `subst`+subsingleton transport. -/
def pf2a : Param map2a map0 (∀ _ : Nat, Nat) (∀ _ : Unary, Unary) :=
  paramForall map2a map0 (RN.weaken rfl rfl) (fun _ _ _ => RN.weaken rfl rfl)
example : pf2a.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl

/- (3,3): full soundness+completeness — needs the domain at class 4. -/
def pf33 : Param map3 map3 (∀ _ : Nat, Nat) (∀ _ : Unary, Unary) :=
  paramForall map3 map3 (RN.weaken rfl rfl) (fun _ _ _ => RN.weaken rfl rfl)
example : pf33.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl

/- (4,4): the full dependent-Π equivalence — the coherence `rInMapK` exists. -/
def pf44 : Param map4 map4 (∀ _ : Nat, Nat) (∀ _ : Unary, Unary) :=
  paramForall map4 map4 (RN.weaken rfl rfl) (fun _ _ _ => RN.weaken rfl rfl)
example : pf44.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl
example : pf44.contra.map (fun u => u) 5 = 5 := rfl                                       -- backward transport
example : ∀ f f' r, pf44.cov.mapInR f f' (pf44.cov.rInMap f f' r) = r := pf44.cov.rInMapK

/-- info: 'LeTrocq.Tests.pf44' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms pf44

/- ===================== a `Prop`-valued dependent goal ===================== -/
/- codomain is a `Prop` family (`0 ≤ ·`), which fits because the hierarchy is over `Sort`. -/
def propPb (n : Nat) (u : Unary) (raa : RNU n u) : Param map1 map1 (0 ≤ n) (0 ≤ Unary.toNat u) where
  R := fun _ _ => PLift True
  cov := { map := fun h => raa.down.symm ▸ h }
  contra := { map := fun h => raa.down ▸ h }

def pfProp : Param map1 map0 (∀ n : Nat, 0 ≤ n) (∀ u : Unary, 0 ≤ Unary.toNat u) :=
  paramForall map1 map0 (RN.weaken rfl rfl) (fun n u raa => (propPb n u raa).weaken rfl rfl)

/- transfer a proof: the `Unary` proposition is obtained from the `Nat` one via the witness. -/
example : (∀ u : Unary, 0 ≤ Unary.toNat u) := pfProp.cov.map (fun n => Nat.zero_le n)

end LeTrocq.Tests
