/-
The LeTrocq STANDARD LIBRARY: `Quot` (the kernel quotient).

`Quot`/`Quot.mk` are kernel constants, but their parametricity registers like any prelude type — NOT a
hardcoded driver primitive. Base-agnostically on BOTH surfaces:
  • the TERM surface (`⟨·⟩`/`[·]`): `QuotRel` is the parametricity RELATION, registered as a TYPE FORMER so
    `⟨·⟩` crosses `Quot r` (counterpart head `Quot ↦ Quot`); `Quot.mk` is a TERM primitive with relatedness `QuotMkR`.
  • the tactic path: the GRADED relator `paramQuotRG`, from a base equivalence + the relations' correspondence.

A quotient is a former over a type `A` AND a relation `r : A → A → Prop` (a TERM argument, relatedness
`rR : … PLift (r a b ↔ r' a' b')`). The parametricity relation is the standard one — related classes have
`RA`-related representatives — stated EXISTENTIALLY so it is well-defined on both quotients and `Prop`-
truncated (a subsingleton, so the `(4,4)` coherence is free).

(`Quot.lift`, the eliminator, is not supported.)
-/
import LeTrocq.Driver.Registry
namespace LeTrocq.Lib
open LeTrocq MapClass

/-- the parametricity relation of `Quot`: related classes have `RA`-related representatives. Existential, so
    well-defined on both quotients by construction; `Prop`-truncated (`PLift` of an `∃`), hence subsingleton.
    A TYPE FORMER keyed by `Quot` (its `(A, A', RA)` and `(r, r', rR)` parameters are supplied by the graded relator `paramQuotRG`). -/
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

/- The shared cov obligations, written ONCE via the raw `pa.cov` fields + the (ungraded) `rR`. `QuotRel` is
   a `Prop`-truncated subsingleton, so `map_in_R` returns `PLift.up …` (a `def`) and coherence is `rfl`. -/
noncomputable def quotFwdMap {A A' : Type} {RA : A → A' → Type} (r : A → A → Prop) (r' : A' → A' → Prop)
    (amap : A → A') (aMapInR : ∀ a a', amap a = a' → RA a a')
    (rR : ∀ a a', RA a a' → ∀ b b', RA b b' → PLift (r a b ↔ r' a' b')) : Quot r → Quot r' :=
  Quot.lift (fun a => Quot.mk r' (amap a)) (fun a b hab =>
    Quot.sound ((rR a (amap a) (aMapInR a (amap a) rfl) b (amap b) (aMapInR b (amap b) rfl)).down.mp hab))

noncomputable def quotMapInR {A A' : Type} {RA : A → A' → Type} (r : A → A → Prop) (r' : A' → A' → Prop)
    (amap : A → A') (aMapInR : ∀ a a', amap a = a' → RA a a')
    (rR : ∀ a a', RA a a' → ∀ b b', RA b b' → PLift (r a b ↔ r' a' b')) :
    ∀ q q', quotFwdMap r r' amap aMapInR rR q = q' → QuotRel A A' RA r r' rR q q' :=
  fun q q' h => PLift.up (by
    obtain ⟨a, ha⟩ := q.exists_rep; subst ha
    exact ⟨a, amap a, rfl, h, ⟨aMapInR a (amap a) rfl⟩⟩)

theorem quotRInMap {A A' : Type} {RA : A → A' → Type} (r : A → A → Prop) (r' : A' → A' → Prop)
    (amap : A → A') (aMapInR : ∀ a a', amap a = a' → RA a a') (aRInMap : ∀ a a', RA a a' → amap a = a')
    (rR : ∀ a a', RA a a' → ∀ b b', RA b b' → PLift (r a b ↔ r' a' b')) :
    ∀ q q', QuotRel A A' RA r r' rR q q' → quotFwdMap r r' amap aMapInR rR q = q' :=
  fun q q' hR => by
    obtain ⟨a, a', ha, ha', ⟨aR⟩⟩ := hR.down; subst ha; subst ha'
    show Quot.mk r' (amap a) = Quot.mk r' a'
    rw [aRInMap a a' aR]

/-- the covariant half from the domain at `mapQuotVariance m`. Coherence is `rfl` (subsingleton relation). -/
noncomputable def quotCov {A A' : Type} (r : A → A → Prop) (r' : A' → A' → Prop) :
    (m : MapClass) →
    (pa : Param (mapQuotVariance m).1 (mapQuotVariance m).2 A A') →
    (rR : (a : A) → (a' : A') → pa.R a a' → (b : A) → (b' : A') → pa.R b b' → PLift (r a b ↔ r' a' b')) →
    MapHas m (QuotRel A A' pa.R r r' rR)
  | map0,  _,  _  => {}
  | map1,  pa, rR => { map := quotFwdMap r r' pa.cov.map pa.cov.map_in_R rR }
  | map2a, pa, rR => { map := quotFwdMap r r' pa.cov.map pa.cov.map_in_R rR,
                       map_in_R := quotMapInR r r' pa.cov.map pa.cov.map_in_R rR }
  | map2b, pa, rR => { map := quotFwdMap r r' pa.cov.map pa.cov.map_in_R rR,
                       R_in_map := quotRInMap r r' pa.cov.map pa.cov.map_in_R pa.cov.R_in_map rR }
  | map3,  pa, rR => { map := quotFwdMap r r' pa.cov.map pa.cov.map_in_R rR,
                       map_in_R := quotMapInR r r' pa.cov.map pa.cov.map_in_R rR,
                       R_in_map := quotRInMap r r' pa.cov.map pa.cov.map_in_R pa.cov.R_in_map rR }
  | map4,  pa, rR => { map := quotFwdMap r r' pa.cov.map pa.cov.map_in_R rR,
                       map_in_R := quotMapInR r r' pa.cov.map pa.cov.map_in_R rR,
                       R_in_map := quotRInMap r r' pa.cov.map pa.cov.map_in_R pa.cov.R_in_map rR,
                       R_in_mapK := fun _ _ _ => rfl }

/- the contra mirror: A-side uses `pa.contra` (`acMap : A' → A`), maps `Quot r' → Quot r` (`.mpr`). -/
noncomputable def quotBwdMap {A A' : Type} {RA : A → A' → Type} (r : A → A → Prop) (r' : A' → A' → Prop)
    (acMap : A' → A) (acMapInR : ∀ a' a, acMap a' = a → RA a a')
    (rR : ∀ a a', RA a a' → ∀ b b', RA b b' → PLift (r a b ↔ r' a' b')) : Quot r' → Quot r :=
  Quot.lift (fun a' => Quot.mk r (acMap a')) (fun a' b' hab =>
    Quot.sound ((rR (acMap a') a' (acMapInR a' (acMap a') rfl)
                    (acMap b') b' (acMapInR b' (acMap b') rfl)).down.mpr hab))

noncomputable def quotContraMapInR {A A' : Type} {RA : A → A' → Type} (r : A → A → Prop) (r' : A' → A' → Prop)
    (acMap : A' → A) (acMapInR : ∀ a' a, acMap a' = a → RA a a')
    (rR : ∀ a a', RA a a' → ∀ b b', RA b b' → PLift (r a b ↔ r' a' b')) :
    ∀ q' q, quotBwdMap r r' acMap acMapInR rR q' = q → QuotRel A A' RA r r' rR q q' :=
  fun q' q h => PLift.up (by
    obtain ⟨a', ha'⟩ := q'.exists_rep; subst ha'
    exact ⟨acMap a', a', h, rfl, ⟨acMapInR a' (acMap a') rfl⟩⟩)

theorem quotContraRInMap {A A' : Type} {RA : A → A' → Type} (r : A → A → Prop) (r' : A' → A' → Prop)
    (acMap : A' → A) (acMapInR : ∀ a' a, acMap a' = a → RA a a') (acRInMap : ∀ a' a, RA a a' → acMap a' = a)
    (rR : ∀ a a', RA a a' → ∀ b b', RA b b' → PLift (r a b ↔ r' a' b')) :
    ∀ q' q, QuotRel A A' RA r r' rR q q' → quotBwdMap r r' acMap acMapInR rR q' = q :=
  fun q' q hR => by
    obtain ⟨a, a', ha, ha', ⟨aR⟩⟩ := hR.down; subst ha; subst ha'
    show Quot.mk r (acMap a') = Quot.mk r a
    rw [acRInMap a' a aR]

/-- the contravariant half from the domain's contra at `mapQuotVariance n`. -/
noncomputable def quotContra {A A' : Type} (r : A → A → Prop) (r' : A' → A' → Prop) :
    (n : MapClass) →
    (pa : Param (mapQuotVariance n).2 (mapQuotVariance n).1 A A') →
    (rR : (a : A) → (a' : A') → pa.R a a' → (b : A) → (b' : A') → pa.R b b' → PLift (r a b ↔ r' a' b')) →
    MapHas n (fun (q' : Quot r') (q : Quot r) => QuotRel A A' pa.R r r' rR q q')
  | map0,  _,  _  => {}
  | map1,  pa, rR => { map := quotBwdMap r r' pa.contra.map pa.contra.map_in_R rR }
  | map2a, pa, rR => { map := quotBwdMap r r' pa.contra.map pa.contra.map_in_R rR,
                       map_in_R := quotContraMapInR r r' pa.contra.map pa.contra.map_in_R rR }
  | map2b, pa, rR => { map := quotBwdMap r r' pa.contra.map pa.contra.map_in_R rR,
                       R_in_map := quotContraRInMap r r' pa.contra.map pa.contra.map_in_R pa.contra.R_in_map rR }
  | map3,  pa, rR => { map := quotBwdMap r r' pa.contra.map pa.contra.map_in_R rR,
                       map_in_R := quotContraMapInR r r' pa.contra.map pa.contra.map_in_R rR,
                       R_in_map := quotContraRInMap r r' pa.contra.map pa.contra.map_in_R pa.contra.R_in_map rR }
  | map4,  pa, rR => { map := quotBwdMap r r' pa.contra.map pa.contra.map_in_R rR,
                       map_in_R := quotContraMapInR r r' pa.contra.map pa.contra.map_in_R rR,
                       R_in_map := quotContraRInMap r r' pa.contra.map pa.contra.map_in_R pa.contra.R_in_map rR,
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

end LeTrocq.Lib
