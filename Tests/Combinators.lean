/- Layer 3 — the combinators: arrow (funext-only), minimal-class arrow (proof-free), universe (no axioms). -/
import Lean
import Trocq.Combinators
namespace Trocq.Tests
open Trocq

/- the arrow's induced forward map is native function transport (B.fwd ∘ f ∘ A.bwd); it COMPUTES: -/
example : arrowNU.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl
example : arrowNU.cov.map (fun n => n + 2) Unary.z = Unary.s (Unary.s Unary.z) := rfl
/- weakened to (1,0) ("just the transported function"), still computing: -/
example : arrowNU_fun.cov.down.map Nat.succ Unary.z = Unary.s Unary.z := rfl
/- the minimal-class arrow gives the backward map (here: backward transport of `id`): -/
example : arrowNU_low.contra.down.map (fun u => u) 5 = 5 := rfl

/- the universe combinator: forward map = `id`, and `map_in_R` produces a real `Param`: -/
example : paramType.cov.map = id := rfl
example : (paramType.cov.map_in_R Nat Nat rfl).cov.down.map = id := rfl

/- axiom footprints — the two boundary facts, pinned:
   arrow at (3,3) costs only funext (Quot.sound); the Type-universe combinator costs nothing. -/
/-- info: 'Trocq.paramArrow33' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms paramArrow33
/-- info: 'Trocq.paramType' does not depend on any axioms -/
#guard_msgs in #print axioms paramType

end Trocq.Tests
