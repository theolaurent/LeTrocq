/- The universe construction: `paramType` at the no-univalence ceiling (2a,2a). -/
import Lean
import Trocq.Combinators.Universe
namespace Trocq.Tests
open Trocq

/- the universe combinator: forward map = `id`, and `map_in_R` produces a real `Param`: -/
example : paramType.cov.map = id := rfl
example : (paramType.cov.map_in_R Nat Nat rfl).cov.down.map = id := rfl

/- the Type-universe combinator is genuinely axiom-free (2a needs no univalence). -/
/-- info: 'Trocq.paramType' does not depend on any axioms -/
#guard_msgs in #print axioms paramType

end Trocq.Tests
