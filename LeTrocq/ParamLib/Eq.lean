/-
The LeTrocq STANDARD LIBRARY: `Eq` (propositional equality).

`a = b` relates to `a' = b'` whenever the underlying type is related by a full equivalence and the two
sides are related pointwise (`aR : pa.R a a'`, `bR : pa.R b b'`). Unlike `List`/`Prod`, equality's
parametricity needs MORE than the bare element relation — it needs the type's `map`/`R_in_map`, i.e. that
the map is a bijection — so `Eq` registers as a RELATOR (whose type argument carries the whole `Param`),
NOT as a prop primitive (which would only expose `.R`).

The forward `a = b → a' = b'` transports along `pa.cov` (`map a = a'`, `map b = b'`, so `a = b` gives
`a' = b'`); the backward direction is the mirror through `pa.contra`. Registered at the top class `(4,4)`:
the two related objects are propositions (subsingletons), so completeness is proof irrelevance and the
coherence is free.

(Monomorphic at `Type`, like the other prelude relators; a `Sort`-polymorphic `Eq` witness is future work.)
-/
import LeTrocq.Attr
namespace LeTrocq.ParamLib
open LeTrocq MapClass

/-- the equality correspondence: `a = b ↔ a' = b'`, both directions transported through `pa`'s maps. -/
theorem eqCorr {A A' : Type} (pa : Param map4 map4 A A')
    {a : A} {a' : A'} (aR : pa.R a a') {b : A} {b' : A'} (bR : pa.R b b') :
    (a = b) ↔ (a' = b') :=
  ⟨fun h => by rw [← pa.cov.R_in_map a a' aR, ← pa.cov.R_in_map b b' bR, h],
   fun h => by rw [← pa.contra.R_in_map a' a aR, ← pa.contra.R_in_map b' b bR, h]⟩

/-- `a = b ≃ a' = b'` at the top class. Its two related objects are `Prop`s, so `R_in_map` (both proofs of
    the same proposition are equal) and the coherence are free by proof irrelevance. A RELATOR keyed by
    `Eq`: its first triple is the TYPE argument (a `Param`), the next two are the term arguments. -/
@[trocq] def paramEqR (A A' : Type) (pa : Param map4 map4 A A')
    (a : A) (a' : A') (aR : pa.R a a') (b : A) (b' : A') (bR : pa.R b b') :
    Param map4 map4 (a = b) (a' = b') where
  R := fun _ _ => PLift ((a = b) ↔ (a' = b'))
  cov :=
    { map := fun h => (eqCorr pa aR bR).mp h
      map_in_R := fun _ _ _ => PLift.up (eqCorr pa aR bR)
      R_in_map := fun _ _ _ => rfl
      R_in_mapK := fun _ _ _ => rfl }
  contra :=
    { map := fun h => (eqCorr pa aR bR).mpr h
      map_in_R := fun _ _ _ => PLift.up (eqCorr pa aR bR)
      R_in_map := fun _ _ _ => rfl
      R_in_mapK := fun _ _ _ => rfl }

end LeTrocq.ParamLib
