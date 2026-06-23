/- The graded hierarchy + weakening (the ⇓ forget maps) over the `Nat ≃ Unary` base. -/
import Lean
import Trocq.Hierarchy
import Examples.NatUnary
namespace Trocq.Tests
open Trocq MapClass Trocq.Examples

/- the forgets COMPUTE: the forward map survives every downgrade, by `rfl`. -/
example : (RN.toRetraction.cov).map = Unary.ofNat := rfl
example : (RN.toSection.cov).map = Unary.ofNat := rfl
example : (RN.toFunction.cov).map = Unary.ofNat := rfl               -- map1 cov: the forward map
example : (RN.toRetraction.contra).map = Unary.toNat := rfl          -- map2a contra: the backward map
/- the soundness field also survives where it should (retraction keeps cov's map_in_R): -/
example : ∀ n u, Unary.ofNat n = u → RNU n u := (RN.toRetraction.cov).map_in_R
/- bottom is the bare relation, with no maps at all: -/
example : (RN.toRel).R = RNU := rfl

/- the section keeps cov's map AND the backward map (contra is map2b = ULift here). -/
example : (RN.toSection.cov).map = Unary.ofNat := rfl
example : (RN.toSection.contra).map = Unary.toNat := rfl

/- the GENERAL `weaken` to arbitrary class pairs preserves the relation + forward map (by `rfl`). -/
def rn_2a2b : Param map2a map2b Nat Unary := RN.weaken rfl rfl
def rn_33   : Param map3 map3   Nat Unary := RN.weaken rfl rfl
def rn_00   : Param map0 map0   Nat Unary := RN.weaken rfl rfl
example : rn_2a2b.cov.map = Unary.ofNat := rfl
example : rn_33.cov.map = Unary.ofNat := rfl
example : rn_00.R = RNU := rfl

/- KEY Lean fact: a class-4 relation is a SUBSINGLETON (`Map4Has.subsingleton`) — this is what makes
   the (4,4) coherence free. `RN`'s relation `RNU n u = PLift (Unary.toNat u = n)` is indeed an h-prop. -/
example (n : Nat) (u : Unary) : Subsingleton (RNU n u) := RN.cov.subsingleton n u
example (n : Nat) (u : Unary) (p q : RNU n u) : p = q := (RN.cov.subsingleton n u).allEq p q

/- the registered base is axiom-free (the 4→3 collapse via proof irrelevance, no univalence). -/
/-- info: 'Trocq.Examples.RN' does not depend on any axioms -/
#guard_msgs in #print axioms RN

end Trocq.Tests
