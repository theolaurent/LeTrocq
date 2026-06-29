/-
The LeTrocq STANDARD LIBRARY: `Quot` (the kernel quotient).

`Quot`/`Quot.mk` are kernel constants, but their parametricity registers like any other prelude type — NOT as
a hardcoded driver primitive. It registers on BOTH surfaces, base-agnostically:

  • the native TRANSLATION (`translate%` / `relate%`): `QuotRel` is the parametricity RELATION (a TYPE FORMER,
    so `paramType` can cross `Quot r`), and the constructor `Quot.mk` is a TERM primitive whose relatedness is
    `QuotMkR`. (Universe-wise this works because `Quot`/`Quot.mk` register through the same
    `mkConstWithFreshMVarLevels` path the driver already used for them.)
  • the SOLVER / tactic path (`trocq` / `transfer%`): the `(4,4)` relator `paramQuotR`, sending a base
    equivalence + the two relations' correspondence to a `Quot` equivalence (the solver weakens it per use).

A quotient is a former over a type `A` AND a relation `r : A → A → Prop`; the relation is a TERM argument, and
(thanks to the `Prop`-relation refinement) its relatedness is the equivalence
`rR : ∀ a a' (aR) b b' (bR), PLift (r a b ↔ r' a' b')` — exactly "`r` and `r'` correspond under the element
relation". The parametricity relation is the standard one (related classes have `RA`-related representatives),
stated EXISTENTIALLY so it is automatically well-defined on both quotients and is `Prop`-truncated (hence a
subsingleton, making the `(4,4)` coherence free).

(`Quot.lift`, the eliminator, is not supported — see the `Quot.lift` note in `LeTrocq.Translate`.)
-/
import LeTrocq.Attr
namespace LeTrocq.ParamLib
open LeTrocq MapClass

/-- the parametricity relation of `Quot`: related classes have `RA`-related representatives. Existential, so
    well-defined on both quotients by construction; `Prop`-truncated (`PLift` of an `∃`), hence subsingleton.
    A TYPE FORMER keyed by `Quot` (its `(A, A', RA)` and `(r, r', rR)` come from `paramType`'s `mkApp3`). -/
@[trocq] def QuotRel (A A' : Type) (RA : A → A' → Type) (r : A → A → Prop) (r' : A' → A' → Prop)
    (_rR : (a : A) → (a' : A') → RA a a' → (b : A) → (b' : A') → RA b b' → PLift (r a b ↔ r' a' b')) :
    Quot r → Quot r' → Type :=
  fun q q' => PLift (∃ a a', Quot.mk r a = q ∧ Quot.mk r' a' = q' ∧ Nonempty (RA a a'))

/-- `Quot.mk r a` relates to `Quot.mk r' a'` whenever the representatives are `RA`-related (witness: itself).
    A TERM primitive keyed by `Quot.mk`. -/
@[trocq] def QuotMkR (A A' : Type) (RA : A → A' → Type) (r : A → A → Prop) (r' : A' → A' → Prop)
    (rR : (a : A) → (a' : A') → RA a a' → (b : A) → (b' : A') → RA b b' → PLift (r a b ↔ r' a' b'))
    (a : A) (a' : A') (aR : RA a a') :
    QuotRel A A' RA r r' rR (Quot.mk r a) (Quot.mk r' a') :=
  PLift.up ⟨a, a', rfl, rfl, ⟨aR⟩⟩

/-- the quotient combinator: `Quot r ≃ Quot r'` from the base equivalence `pa` and the correspondence `rR` of
    the two relations. The maps are `Quot.lift`s of `pa`'s maps; they respect the relations because `rR` turns
    `r a b` into `r' (map a) (map b)` (then `Quot.sound`). Completeness picks a representative
    (`Quot.exists_rep`) and stays in `Prop`; the coherence is free (the relation is a subsingleton). A RELATOR
    keyed by `Quot` (concl `Param … (Quot r) (Quot r')`). -/
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

end LeTrocq.ParamLib
