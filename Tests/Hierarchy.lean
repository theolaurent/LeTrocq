/- Layer 2 — the graded hierarchy + weakening (the ⇓ forget maps) over the `Nat ≃ Unary` base. -/
import Lean
import Trocq.Hierarchy
namespace Trocq.Tests
open Trocq

/- the forgets COMPUTE: the forward map survives every downgrade, by `rfl`. -/
example : (RN.toRetraction.cov).map = ofNat := rfl
example : (RN.toSection.cov).map = ofNat := rfl
example : (RN.toFunction.cov).down.map = ofNat := rfl          -- map1 cov is ULift-wrapped
example : (RN.toRetraction.contra).map = toNat := rfl          -- map2a contra: the backward map
/- the soundness field also survives where it should (retraction keeps cov's map_in_R): -/
example : ∀ n u, ofNat n = u → RNU n u := (RN.toRetraction.cov).map_in_R
/- bottom is the bare relation, with no maps at all: -/
example : (RN.toRel).R = RNU := rfl

/- the registered base is axiom-free (the 4→3 collapse via proof irrelevance, no univalence). -/
/-- info: 'Trocq.RN' does not depend on any axioms -/
#guard_msgs in #print axioms RN

end Trocq.Tests
