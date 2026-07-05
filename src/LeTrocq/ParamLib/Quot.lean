/-
The LeTrocq STANDARD LIBRARY: `Quot` (the kernel quotient).

`Quot`/`Quot.mk` are kernel constants, but their parametricity registers like any prelude type — NOT a
hardcoded driver primitive. Base-agnostically on BOTH surfaces:
  • the TERM surface (`⟨·⟩`/`[·]`): `QuotRel` is the parametricity RELATION (a TYPE FORMER, so `paramType`
    crosses `Quot r`); `Quot.mk` is a TERM primitive with relatedness `QuotMkR`.
  • the tactic path: the GRADED relator `paramQuotRG`, from a base equivalence + the relations' correspondence.

A quotient is a former over a type `A` AND a relation `r : A → A → Prop` (a TERM argument, relatedness
`rR : … PLift (r a b ↔ r' a' b')`). The parametricity relation is the standard one — related classes have
`RA`-related representatives — stated EXISTENTIALLY so it is well-defined on both quotients and `Prop`-
truncated (a subsingleton, so the `(4,4)` coherence is free).

(`Quot.lift`, the eliminator, is not supported.)
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

/- ===================== the GRADED relator (variance mechanism, dependent — domain only) =====================
   Only the base `A` is graded: `r`/`r'` are a TERM argument and `rR` its (ungraded) relatedness. `Quot`'s
   relation is `Prop`-truncated (a `PLift` of an `∃`), so it is ALWAYS a subsingleton — the coherence
   `R_in_mapK` is `rfl` for FREE, with no class-4 requirement on `pa`. But the forward map's well-definedness
   uses `pa.cov.map_in_R` (soundness, 2a) at EVERY class ≥ 1, so an output that wants completeness (`R_in_map`,
   2b) forces `pa` to `map3` (both `map_in_R` and `R_in_map`); `map4` needs no more than `map3` (coherence free). -/

/-- per-map-class minimal DOMAIN class for `Quot` (the map needs 2a everywhere; completeness forces map3). -/
def mapQuotVariance : MapClass → ParamClass
  | map0  => (map0,  map0)
  | map1  => (map2a, map0)
  | map2a => (map2a, map0)
  | map2b => (map3,  map0)
  | map3  => (map3,  map0)
  | map4  => (map3,  map0)

/-- minimal domain class to build `Quot` at output class `c` (cov joined with negated contra). -/
def quotVariance (c : ParamClass) : ParamClass :=
  ParamClass.join (mapQuotVariance c.1) (ParamClass.negate (mapQuotVariance c.2))

/-- the covariant half from the domain at `mapQuotVariance m`. Coherence is `rfl` (subsingleton relation). -/
noncomputable def quotCov {A A' : Type} (r : A → A → Prop) (r' : A' → A' → Prop) :
    (m : MapClass) →
    (pa : Param (mapQuotVariance m).1 (mapQuotVariance m).2 A A') →
    (rR : (a : A) → (a' : A') → pa.R a a' → (b : A) → (b' : A') → pa.R b b' → PLift (r a b ↔ r' a' b')) →
    MapHas m (QuotRel A A' pa.R r r' rR)
  | map0,  _,  _  => {}
  | map1,  pa, rR =>
      { map := Quot.lift (fun a => Quot.mk r' (pa.cov.map a)) (fun a b hab =>
          Quot.sound ((rR a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)
                          b (pa.cov.map b) (pa.cov.map_in_R b _ rfl)).down.mp hab)) }
  | map2a, pa, rR =>
      { map := Quot.lift (fun a => Quot.mk r' (pa.cov.map a)) (fun a b hab =>
          Quot.sound ((rR a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)
                          b (pa.cov.map b) (pa.cov.map_in_R b _ rfl)).down.mp hab))
        map_in_R := fun q q' h => PLift.up (by
          obtain ⟨a, ha⟩ := q.exists_rep; subst ha
          exact ⟨a, pa.cov.map a, rfl, h, ⟨pa.cov.map_in_R a _ rfl⟩⟩) }
  | map2b, pa, rR =>
      { map := Quot.lift (fun a => Quot.mk r' (pa.cov.map a)) (fun a b hab =>
          Quot.sound ((rR a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)
                          b (pa.cov.map b) (pa.cov.map_in_R b _ rfl)).down.mp hab))
        R_in_map := fun q q' hR => by
          obtain ⟨a, a', ha, ha', ⟨aR⟩⟩ := hR.down; subst ha; subst ha'
          show Quot.mk r' (pa.cov.map a) = Quot.mk r' a'
          rw [pa.cov.R_in_map a a' aR] }
  | map3,  pa, rR =>
      { map := Quot.lift (fun a => Quot.mk r' (pa.cov.map a)) (fun a b hab =>
          Quot.sound ((rR a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)
                          b (pa.cov.map b) (pa.cov.map_in_R b _ rfl)).down.mp hab))
        map_in_R := fun q q' h => PLift.up (by
          obtain ⟨a, ha⟩ := q.exists_rep; subst ha
          exact ⟨a, pa.cov.map a, rfl, h, ⟨pa.cov.map_in_R a _ rfl⟩⟩)
        R_in_map := fun q q' hR => by
          obtain ⟨a, a', ha, ha', ⟨aR⟩⟩ := hR.down; subst ha; subst ha'
          show Quot.mk r' (pa.cov.map a) = Quot.mk r' a'
          rw [pa.cov.R_in_map a a' aR] }
  | map4,  pa, rR =>
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

/-- the contravariant half from the domain's contra at `mapQuotVariance n`. -/
noncomputable def quotContra {A A' : Type} (r : A → A → Prop) (r' : A' → A' → Prop) :
    (n : MapClass) →
    (pa : Param (mapQuotVariance n).2 (mapQuotVariance n).1 A A') →
    (rR : (a : A) → (a' : A') → pa.R a a' → (b : A) → (b' : A') → pa.R b b' → PLift (r a b ↔ r' a' b')) →
    MapHas n (fun (q' : Quot r') (q : Quot r) => QuotRel A A' pa.R r r' rR q q')
  | map0,  _,  _  => {}
  | map1,  pa, rR =>
      { map := Quot.lift (fun a' => Quot.mk r (pa.contra.map a')) (fun a' b' hab =>
          Quot.sound ((rR (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)
                          (pa.contra.map b') b' (pa.contra.map_in_R b' _ rfl)).down.mpr hab)) }
  | map2a, pa, rR =>
      { map := Quot.lift (fun a' => Quot.mk r (pa.contra.map a')) (fun a' b' hab =>
          Quot.sound ((rR (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)
                          (pa.contra.map b') b' (pa.contra.map_in_R b' _ rfl)).down.mpr hab))
        map_in_R := fun q' q h => PLift.up (by
          obtain ⟨a', ha'⟩ := q'.exists_rep; subst ha'
          exact ⟨pa.contra.map a', a', h, rfl, ⟨pa.contra.map_in_R a' _ rfl⟩⟩) }
  | map2b, pa, rR =>
      { map := Quot.lift (fun a' => Quot.mk r (pa.contra.map a')) (fun a' b' hab =>
          Quot.sound ((rR (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)
                          (pa.contra.map b') b' (pa.contra.map_in_R b' _ rfl)).down.mpr hab))
        R_in_map := fun q' q hR => by
          obtain ⟨a, a', ha, ha', ⟨aR⟩⟩ := hR.down; subst ha; subst ha'
          show Quot.mk r (pa.contra.map a') = Quot.mk r a
          rw [pa.contra.R_in_map a' a aR] }
  | map3,  pa, rR =>
      { map := Quot.lift (fun a' => Quot.mk r (pa.contra.map a')) (fun a' b' hab =>
          Quot.sound ((rR (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)
                          (pa.contra.map b') b' (pa.contra.map_in_R b' _ rfl)).down.mpr hab))
        map_in_R := fun q' q h => PLift.up (by
          obtain ⟨a', ha'⟩ := q'.exists_rep; subst ha'
          exact ⟨pa.contra.map a', a', h, rfl, ⟨pa.contra.map_in_R a' _ rfl⟩⟩)
        R_in_map := fun q' q hR => by
          obtain ⟨a, a', ha, ha', ⟨aR⟩⟩ := hR.down; subst ha; subst ha'
          show Quot.mk r (pa.contra.map a') = Quot.mk r a
          rw [pa.contra.R_in_map a' a aR] }
  | map4,  pa, rR =>
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

/-- `Quot r ≃ Quot r'` at ANY output class `(m,n)`, domain at the `quotVariance`-minimal class. -/
@[trocq] noncomputable def paramQuotRG (m n : MapClass) (A A' : Type)
    (pa : Param (quotVariance (m, n)).1 (quotVariance (m, n)).2 A A')
    (r : A → A → Prop) (r' : A' → A' → Prop)
    (rR : (a : A) → (a' : A') → pa.R a a' → (b : A) → (b' : A') → pa.R b b' → PLift (r a b ↔ r' a' b')) :
    Param m n (Quot r) (Quot r') where
  R := QuotRel A A' pa.R r r' rR
  cov := quotCov r r' m (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) rR
  contra := quotContra r r' n (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) rR

end LeTrocq.ParamLib
