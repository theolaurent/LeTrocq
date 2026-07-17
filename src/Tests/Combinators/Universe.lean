/- The universe construction: `paramTypeAt` at the no-univalence ceiling (2a,2a). -/
import Lean
import LeTrocq.Combinators.Universe
namespace LeTrocq.Tests
open LeTrocq MapClass

/- the universe combinator at the ceiling: forward map = `id`, `mapInR` produces a real `Param`. -/
example : (paramTypeAt map2a map2a map1 map1 rfl rfl).cov.map = id := rfl
example : ((paramTypeAt map2a map2a map1 map1 rfl rfl).cov.mapInR Nat Nat rfl).cov.map = id := rfl

/- the reflexive identity at the top class computes (map = id) and carries the coherence field. -/
example : (paramRefl Nat).cov.map = id := rfl
example : ∀ a b r, (paramRefl Nat).cov.mapInR a b ((paramRefl Nat).cov.rInMap a b r) = r :=
  (paramRefl Nat).cov.rInMapK
example : (paramIdAt map4 map4 Nat).cov.map = id := rfl
example : (paramIdAt map1 map1 Nat).cov.map = id := rfl

/- the combinator carries any inner relation class, independent of the (≤2a) outer class. -/
example : (paramTypeAt map2a map2a map3 map3 rfl rfl).cov.map = id := rfl
example : ((paramTypeAt map2a map2a map3 map3 rfl rfl).cov.mapInR Nat Nat rfl).cov.map = id := rfl
example : (paramTypeAt map1 map0 map4 map4 rfl rfl).cov.map = id := rfl

/- the Type-universe combinators are genuinely axiom-free (2a needs no univalence). -/
/-- info: 'LeTrocq.paramTypeAt' does not depend on any axioms -/
#guard_msgs in #print axioms paramTypeAt
/-- info: 'LeTrocq.paramRefl' does not depend on any axioms -/
#guard_msgs in #print axioms paramRefl

/- the `Prop` universe combinator reaches the full (4,4) — completeness via `propext`, coherence free
   by proof irrelevance — where the `Type` universe stalls at 2a. -/
example : paramProp.cov.map = id := rfl
example : ∀ P P' r, paramProp.cov.mapInR P P' (paramProp.cov.rInMap P P' r) = r := paramProp.cov.rInMapK
example : (paramPropAt map2a map0).cov.map = id := rfl
/-- info: 'LeTrocq.paramProp' does not depend on any axioms -/
#guard_msgs in #print axioms paramProp

end LeTrocq.Tests
