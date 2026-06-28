/-
Registering QUOTIENTS: Lean's `Quot {α} (r : α → α → Prop)`.

A quotient is a former applied to a type `α` AND a relation `r : α → α → Prop`. The relation is an ordinary
TERM argument — no new driver machinery — and thanks to the `Prop`-relation refinement its relatedness is the
logical-equivalence `rR : ∀ a a' (aR) b b' (bR), PLift (r a b ↔ r' a' b')`, i.e. exactly "`r` and `r'`
correspond under the element relation". That is what makes quotient transport go through.

The parametricity relation is the standard one: two classes are related iff they have `RA`-related
representatives. Stated EXISTENTIALLY (`∃` related reps), it is automatically well-defined on the quotients —
no `Quot.lift` is needed to even DEFINE it — and it is `Prop`-truncated (so a subsingleton, making the `(4,4)`
coherence free). The maps in the relator ARE `Quot.lift`s, and respect-of-the-relation comes from `rR`.

  • TRANSLATION: `QuotRel` (type former) + `Quot.mk` (term primitive).
  • TACTIC: `paramQuotR`, the `(4,4)` relator.
-/
import Trocq
namespace Trocq.Examples
open Trocq MapClass

/-- the parametricity relation of `Quot`: related classes have `RA`-related representatives. Existential, so
    well-defined on both quotients by construction; `Prop`-truncated (`PLift` of an `∃`), hence subsingleton. -/
@[trocq] def QuotRel (A A' : Type) (RA : A → A' → Type) (r : A → A → Prop) (r' : A' → A' → Prop)
    (_rR : (a : A) → (a' : A') → RA a a' → (b : A) → (b' : A') → RA b b' → PLift (r a b ↔ r' a' b')) :
    Quot r → Quot r' → Type :=
  fun q q' => PLift (∃ a a', Quot.mk r a = q ∧ Quot.mk r' a' = q' ∧ Nonempty (RA a a'))

/-- `Quot.mk r a` relates to `Quot.mk r' a'` whenever the representatives are `RA`-related (witness: itself). -/
@[trocq] def QuotMkR (A A' : Type) (RA : A → A' → Type) (r : A → A → Prop) (r' : A' → A' → Prop)
    (rR : (a : A) → (a' : A') → RA a a' → (b : A) → (b' : A') → RA b b' → PLift (r a b ↔ r' a' b'))
    (a : A) (a' : A') (aR : RA a a') :
    QuotRel A A' RA r r' rR (Quot.mk r a) (Quot.mk r' a') :=
  PLift.up ⟨a, a', rfl, rfl, ⟨aR⟩⟩

/- ===================== the `(4,4)` relator (for the `trocq` / `transfer%` tactic) =====================
   `Quot r ≃ Quot r'` from the base equivalence `pa` and the correspondence `rR` of the two quotient relations.
   The maps are `Quot.lift`s of `pa`'s maps; they respect the relations because `rR` turns `r a b` into
   `r' (map a) (map b)` (then `Quot.sound`). Completeness picks a representative (`Quot.exists_rep`) and stays
   in `Prop`; the coherence is free since the relation is a `Prop`-truncated subsingleton. -/
@[trocq] noncomputable def paramQuotR (A A' : Type) (pa : Param map4 map4 A A')
    (r : A → A → Prop) (r' : A' → A' → Prop)
    (rR : (a : A) → (a' : A') → pa.R a a' → (b : A) → (b' : A') → pa.R b b' → PLift (r a b ↔ r' a' b')) :
    Param map4 map4 (Quot r) (Quot r') where
  R := QuotRel A A' pa.R r r' rR
  cov :=
    { map := Quot.lift (fun a => Quot.mk r' (pa.cov.map a)) (fun a b hab =>
        Quot.sound ((rR a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)
                        b (pa.cov.map b) (pa.cov.map_in_R b _ rfl)).down.mp hab))
      map_in_R := fun q q' h => PLift.up (by
        obtain ⟨a, ha⟩ := q.exists_rep; subst ha
        exact ⟨a, pa.cov.map a, rfl, h, ⟨pa.cov.map_in_R a _ rfl⟩⟩)
      R_in_map := fun q q' hR => by
        obtain ⟨a, a', ha, ha', ⟨aR⟩⟩ := hR.down; subst ha; subst ha'
        show Quot.mk r' (pa.cov.map a) = Quot.mk r' a'
        rw [pa.cov.R_in_map a a' aR]
      R_in_mapK := fun _ _ _ => rfl }
  contra :=
    { map := Quot.lift (fun a' => Quot.mk r (pa.contra.map a')) (fun a' b' hab =>
        Quot.sound ((rR (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)
                        (pa.contra.map b') b' (pa.contra.map_in_R b' _ rfl)).down.mpr hab))
      map_in_R := fun q' q h => PLift.up (by
        obtain ⟨a', ha'⟩ := q'.exists_rep; subst ha'
        exact ⟨pa.contra.map a', a', h, rfl, ⟨pa.contra.map_in_R a' _ rfl⟩⟩)
      R_in_map := fun q' q hR => by
        obtain ⟨a, a', ha, ha', ⟨aR⟩⟩ := hR.down; subst ha; subst ha'
        show Quot.mk r (pa.contra.map a') = Quot.mk r a
        rw [pa.contra.R_in_map a' a aR]
      R_in_mapK := fun _ _ _ => rfl }

end Trocq.Examples
