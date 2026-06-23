/- The universe construction: `paramType` at the no-univalence ceiling (2a,2a). -/
import Lean
import Trocq.Combinators.Universe
namespace Trocq.Tests
open Trocq MapClass

/- the universe combinator: forward map = `id`, and `map_in_R` produces a real `Param`: -/
example : paramType.cov.map = id := rfl
example : (paramType.cov.map_in_R Nat Nat rfl).cov.down.map = id := rfl

/- the reflexive identity at the top class computes (map = id) and carries the coherence field. -/
example : (paramRefl Nat).cov.map = id := rfl
example : ∀ a b r, (paramRefl Nat).cov.map_in_R a b ((paramRefl Nat).cov.R_in_map a b r) = r :=
  (paramRefl Nat).cov.R_in_mapK
example : (paramIdAt map4 map4 Nat).cov.map = id := rfl
example : (paramIdAt map1 map1 Nat).cov.down.map = id := rfl

/- `Map_Type`: the universe combinator can carry ANY inner relation class, independent of the (≤2a)
   outer class — here inner (3,3), and inner (4,4) at a lower outer class. -/
example : (paramTypeAtInner map2a map2a map3 map3 rfl rfl).cov.map = id := rfl
example : ((paramTypeAtInner map2a map2a map3 map3 rfl rfl).cov.map_in_R Nat Nat rfl).cov.map = id := rfl
example : (paramTypeAtInner map1 map0 map4 map4 rfl rfl).cov.down.map = id := rfl

/- the Type-universe combinators are genuinely axiom-free (2a needs no univalence). -/
/-- info: 'Trocq.paramType' does not depend on any axioms -/
#guard_msgs in #print axioms paramType
/-- info: 'Trocq.paramRefl' does not depend on any axioms -/
#guard_msgs in #print axioms paramRefl

end Trocq.Tests
