/-
The LeTrocq STANDARD LIBRARY: `Eq` (propositional equality).

`a = b` relates to `a' = b'` whenever the underlying type is related by a full equivalence and the two
sides are related pointwise (`aR : pa.R a a'`, `bR : pa.R b b'`). Unlike `List`/`Prod`, equality's
parametricity needs MORE than the bare element relation — it needs the type's `map`/`R_in_map`, i.e. that
the map is a bijection — so `Eq`'s type argument is carried as a whole `Param` (not just its `.R` relation),
which the RELATOR classification provides.

The forward `a = b → a' = b'` transports along `pa.cov` (`map a = a'`, `map b = b'`, so `a = b` gives
`a' = b'`); the backward direction is the mirror through `pa.contra`. Registered at the top class `(4,4)`:
the two related objects are propositions (subsingletons), so completeness is proof irrelevance and the
coherence is free.

(Monomorphic at `Type`, like the other prelude relators; a `Sort`-polymorphic `Eq` witness is future work.)
-/
import LeTrocq.Attr
import LeTrocq.ParamCC.Universe
namespace LeTrocq.ParamLib
open LeTrocq MapClass

/-- the equality correspondence: `a = b ↔ a' = b'`, both directions transported through `pa`'s maps. -/
theorem eqCorr {A A' : Type} (pa : Param map4 map4 A A')
    {a : A} {a' : A'} (aR : pa.R a a') {b : A} {b' : A'} (bR : pa.R b b') :
    (a = b) ↔ (a' = b') :=
  ⟨fun h => by rw [← pa.cov.R_in_map a a' aR, ← pa.cov.R_in_map b b' bR, h],
   fun h => by rw [← pa.contra.R_in_map a' a aR, ← pa.contra.R_in_map b' b bR, h]⟩

/-- `a = b ≃ a' = b'` at the top class, carrying `〚Prop〛 = PLift (·↔·)` (via `paramOfIff`). A RELATOR keyed
    by `Eq`: its first triple is the TYPE argument (a `Param`), the next two are the term arguments. -/
@[trocq] def paramEqR (A A' : Type) (pa : Param map4 map4 A A')
    (a : A) (a' : A') (aR : pa.R a a') (b : A) (b' : A') (bR : pa.R b b') :
    Param map4 map4 (a = b) (a' = b') := paramOfIff (eqCorr pa aR bR)

end LeTrocq.ParamLib
