/- The universe construction: `paramType` at the no-univalence ceiling (2a,2a). -/
import Lean
import LeTrocq.Core.Universe
namespace LeTrocq.Tests
open LeTrocq MapClass

/- the universe combinator: forward map = `id`, and `map_in_R` produces a real `Param`: -/
example : paramType.cov.map = id := rfl
example : (paramType.cov.map_in_R Nat Nat rfl).cov.map = id := rfl

/- the reflexive identity at the top class computes (map = id) and carries the coherence field. -/
example : (paramRefl Nat).cov.map = id := rfl
example : ∀ a b r, (paramRefl Nat).cov.map_in_R a b ((paramRefl Nat).cov.R_in_map a b r) = r :=
  (paramRefl Nat).cov.R_in_mapK
example : (paramIdAt map4 map4 Nat).cov.map = id := rfl
example : (paramIdAt map1 map1 Nat).cov.map = id := rfl

/- `Map_Type`: the universe combinator can carry ANY inner relation class, independent of the (≤2a)
   outer class — here inner (3,3), and inner (4,4) at a lower outer class. -/
example : (paramTypeAtInner map2a map2a map3 map3 rfl rfl).cov.map = id := rfl
example : ((paramTypeAtInner map2a map2a map3 map3 rfl rfl).cov.map_in_R Nat Nat rfl).cov.map = id := rfl
example : (paramTypeAtInner map1 map0 map4 map4 rfl rfl).cov.map = id := rfl

/- the Type-universe combinators are genuinely axiom-free (2a needs no univalence). -/
/-- info: 'LeTrocq.paramType' does not depend on any axioms -/
#guard_msgs in #print axioms paramType
/-- info: 'LeTrocq.paramRefl' does not depend on any axioms -/
#guard_msgs in #print axioms paramRefl

/- the PROP universe combinator reaches the FULL (4,4) — completeness via `propext`, coherence free by
   proof irrelevance — where the `Type` universe stalls at 2a. -/
example : paramProp.cov.map = id := rfl
example : ∀ P P' r, paramProp.cov.map_in_R P P' (paramProp.cov.R_in_map P P' r) = r := paramProp.cov.R_in_mapK
example : (paramPropAt map2a map0).cov.map = id := rfl
/-- info: 'LeTrocq.paramProp' depends on axioms: [propext] -/
#guard_msgs in #print axioms paramProp

end LeTrocq.Tests
