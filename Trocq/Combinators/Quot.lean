/-
The QUOTIENT construction: relating `Quot r` to `Quot r'`.

`Quot` is a kernel PRIMITIVE (like `Sort`), so — unlike `List`/`Sigma`, which a user registers with `@[trocq]`
— its parametricity is part of the library and the driver knows it intrinsically (`paramType`/`param` for
`Quot`/`Quot.mk`, `buildConsts` for the relator, and a `param` special-case for `Quot.lift`).

A quotient is a former over a type `A` AND a relation `r : A → A → Prop`; the relation is a TERM argument,
and (thanks to the `Prop`-relation refinement) its relatedness is the equivalence
`rR : ∀ a a' (aR) b b' (bR), PLift (r a b ↔ r' a' b')` — exactly "`r` and `r'` correspond under the element
relation". The parametricity relation is the standard one (related classes have `RA`-related representatives),
stated EXISTENTIALLY so it is automatically well-defined on both quotients and is `Prop`-truncated (hence a
subsingleton, making the `(4,4)` coherence free).
-/
import Trocq.Hierarchy
namespace Trocq
open MapClass

/-- the parametricity relation of `Quot`: related classes have `RA`-related representatives. Existential, so
    well-defined on both quotients by construction; `Prop`-truncated (`PLift` of an `∃`), hence subsingleton. -/
def QuotRel (A A' : Type) (RA : A → A' → Type) (r : A → A → Prop) (r' : A' → A' → Prop)
    (_rR : (a : A) → (a' : A') → RA a a' → (b : A) → (b' : A') → RA b b' → PLift (r a b ↔ r' a' b')) :
    Quot r → Quot r' → Type :=
  fun q q' => PLift (∃ a a', Quot.mk r a = q ∧ Quot.mk r' a' = q' ∧ Nonempty (RA a a'))

/-- `Quot.mk r a` relates to `Quot.mk r' a'` whenever the representatives are `RA`-related (witness: itself). -/
def QuotMkR (A A' : Type) (RA : A → A' → Type) (r : A → A → Prop) (r' : A' → A' → Prop)
    (rR : (a : A) → (a' : A') → RA a a' → (b : A) → (b' : A') → RA b b' → PLift (r a b ↔ r' a' b'))
    (a : A) (a' : A') (aR : RA a a') :
    QuotRel A A' RA r r' rR (Quot.mk r a) (Quot.mk r' a') :=
  PLift.up ⟨a, a', rfl, rfl, ⟨aR⟩⟩

/-- the quotient combinator: `Quot r ≃ Quot r'` from the base equivalence `pa` and the correspondence `rR` of
    the two relations. The maps are `Quot.lift`s of `pa`'s maps; they respect the relations because `rR` turns
    `r a b` into `r' (map a) (map b)` (then `Quot.sound`). Completeness picks a representative
    (`Quot.exists_rep`) and stays in `Prop`; the coherence is free (the relation is a subsingleton). -/
noncomputable def paramQuotR (A A' : Type) (pa : Param map4 map4 A A')
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

/- ===================== `Quot.lift`: the eliminator (special-cased in `param`) =====================
   `Quot.lift f h : Quot r → β` transports to `Quot.lift f' h' : Quot r' → β'`. The respect proof
   `h' : ∀ a' b', r' a' b' → f' a' = f' b'` cannot be got from the relations alone (translate is map-free):
   `quotLiftResp` SYNTHESISES it from the domain/codomain base equivalences — pull `a' b'` back, use `rR`,
   the original `h`, then `fR` + the codomain map. `quotLiftRel` is the eliminator's parametricity. -/
theorem quotLiftResp {A A' B B' : Type} (pa : Param map4 map4 A A') (pb : Param map4 map4 B B')
    {r : A → A → Prop} {r' : A' → A' → Prop} {f : A → B} {f' : A' → B'}
    (rR : (a : A) → (a' : A') → pa.R a a' → (b : A) → (b' : A') → pa.R b b' → PLift (r a b ↔ r' a' b'))
    (fR : (a : A) → (a' : A') → pa.R a a' → pb.R (f a) (f' a'))
    (h : ∀ a b, r a b → f a = f b) : ∀ a' b', r' a' b' → f' a' = f' b' := by
  intro a' b' hr'
  have aR := pa.contra.map_in_R a' (pa.contra.map a') rfl
  have bR := pa.contra.map_in_R b' (pa.contra.map b') rfl
  have e1 : pb.cov.map (f (pa.contra.map a')) = f' a' := pb.cov.R_in_map _ _ (fR _ a' aR)
  have e2 : pb.cov.map (f (pa.contra.map b')) = f' b' := pb.cov.R_in_map _ _ (fR _ b' bR)
  rw [← e1, ← e2, h _ _ ((rR _ a' aR _ b' bR).down.mpr hr')]

noncomputable def quotLiftRel {A A' B B' : Type} (pa : Param map4 map4 A A') (pb : Param map4 map4 B B')
    {r : A → A → Prop} {r' : A' → A' → Prop}
    (rR : (a : A) → (a' : A') → pa.R a a' → (b : A) → (b' : A') → pa.R b b' → PLift (r a b ↔ r' a' b'))
    {f : A → B} {f' : A' → B'}
    (fR : (a : A) → (a' : A') → pa.R a a' → pb.R (f a) (f' a'))
    (h : ∀ a b, r a b → f a = f b) (h' : ∀ a' b', r' a' b' → f' a' = f' b')
    (q : Quot r) (q' : Quot r') (qR : QuotRel A A' pa.R r r' rR q q') :
    pb.R (Quot.lift f h q) (Quot.lift f' h' q') :=
  -- the quotient relation is `Prop`-truncated, so we cannot `cases` it into the `Type`-valued `pb.R`; but
  -- `pb.R` is a subsingleton at `(4,4)`, so prove `Nonempty` (in `Prop`) then `Classical.choice`.
  Classical.choice (by
    obtain ⟨a, a', ha, ha', ⟨aR⟩⟩ := qR.down; subst ha; subst ha'
    exact ⟨fR a a' aR⟩)

end Trocq
