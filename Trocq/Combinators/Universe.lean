/-
The UNIVERSE construction: relating `Type` to `Type`.

The no-univalence ceiling is class (2a,2a): `map_in_R : A = A' → Param A A'` is `Eq.rec` (free), but the
completeness field `R_in_map : Param A A' → A = A'` would need univalence — so `Type` is BLOCKED above 2a,
exactly what Layer 1's `requiresAxiom`/`depType` encode. `paramTypeAt` weakens the ceiling to any lower class.
-/
import Trocq.Hierarchy
universe u
namespace Trocq
open MapClass

/-- a reflexive `Param` at (1,1): the identity, with `R a b := PLift (a = b)`. -/
def paramId (A : Type 0) : Param.{0,0} map1 map1 A A where
  R := fun a b => PLift (a = b)
  cov := ULift.up { map := id }
  contra := ULift.up { map := id }

/-- the universe combinator at the ceiling (2a,2a). The relation on types IS `Param 1 1`; the forward
    map is `id` and `map_in_R` is `Eq.rec` of `paramId` — no univalence. -/
def paramType : Param.{1,1} map2a map2a (Type 0) (Type 0) where
  R := fun A A' => Param.{0,0} map1 map1 A A'
  cov :=
    { map := id
      map_in_R := fun A A' h => by subst h; exact paramId A }
  contra :=
    { map := id
      map_in_R := fun A' A h => by subst h; exact paramId A' }

/-- the universe combinator at ANY class `≤ (2a,2a)`, by weakening `paramType`. -/
def paramTypeAt (m n : MapClass)
    (hm : MapClass.le m map2a = true) (hn : MapClass.le n map2a = true) :
    Param.{1,1} m n (Type 0) (Type 0) :=
  paramType.weaken hm hn

end Trocq
