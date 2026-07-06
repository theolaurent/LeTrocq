/-
The LeTrocq STANDARD LIBRARY: `Eq` (propositional equality).

`a = b` relates to `a' = b'` when the underlying type is a FULL equivalence and the two sides are related
pointwise. Unlike `List`/`Prod`, equality needs more than the bare element relation — it needs the map to
be a bijection (`eqCorr` uses both `rInMap`s) — so `Eq`'s type argument is a whole `Param map4 map4`,
fixed at (4,4) regardless of the output class. The two related objects are propositions, so completeness is
proof irrelevance and the coherence is free.

(Monomorphic at `Type`; a `Sort`-polymorphic `Eq` witness is future work.)
-/
import LeTrocq.Driver.Registry
import LeTrocq.Combinators.Universe
namespace LeTrocq.Lib
open LeTrocq MapClass

/-- the equality correspondence: `a = b ↔ a' = b'`, both directions transported through `pa`'s maps. -/
theorem eqCorr {A A' : Type} (pa : Param map4 map4 A A')
    {a : A} {a' : A'} (aRel : pa.R a a') {b : A} {b' : A'} (bRel : pa.R b b') :
    (a = b) ↔ (a' = b') :=
  ⟨fun h => by rw [← pa.cov.rInMap a a' aRel, ← pa.cov.rInMap b b' bRel, h],
   fun h => by rw [← pa.contra.rInMap a' a aRel, ← pa.contra.rInMap b' b bRel, h]⟩

/-- `a = b ≃ a' = b'` at any output class `(m,n)`, from the correspondence `eqCorr` via `paramPropFromMaps`
    (relation `fun _ _ => PLift True`). A RELATOR keyed by `Eq`: first triple is the TYPE argument
    (a `Param map4 map4`), the next two are the term arguments. -/
@[trocq] def paramEq (m n : MapClass) (A A' : Type) (pa : Param map4 map4 A A')
    (a : A) (a' : A') (aRel : pa.R a a') (b : A) (b' : A') (bRel : pa.R b b') :
    Param m n (a = b) (a' = b') :=
  paramPropFromMaps m n (eqCorr pa aRel bRel).mp (eqCorr pa aRel bRel).mpr

end LeTrocq.Lib
