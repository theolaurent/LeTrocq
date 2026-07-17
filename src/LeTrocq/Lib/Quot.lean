/-
`Quot` (the kernel quotient former) — standard-library registration. `Quot`/`Quot.mk` are kernel constants,
but their parametricity registers like any prelude type, NOT a hardcoded driver primitive. `QuotRel` is the
parametricity relation (a TYPE FORMER, so `⟨·⟩` crosses `Quot r`); `Quot.mk` is a term primitive with
relatedness `QuotMkR`; `paramQuot` is the graded relator. A quotient is a former over a type `A` AND a
relation `r` (a TERM argument, relatedness `rR`).

(`Quot.lift`, the eliminator, is not supported.)
-/
import LeTrocq.Driver.Registry
namespace LeTrocq.Lib
open LeTrocq MapClass

/-- the parametricity relation of `Quot`: related classes have `RA`-related representatives, stated
    existentially so it is well-defined on both quotients; `Prop`-truncated (`PLift` of an `∃`), hence
    subsingleton (the `(4,4)` coherence is free). The `Quot` type former. -/
@[trocq] def QuotRel (A A' : Type) (RA : A → A' → Type) (r : A → A → Prop) (r' : A' → A' → Prop)
    (_rR : (a : A) → (a' : A') → RA a a' → (b : A) → (b' : A') → RA b b' → PLift (r a b ↔ r' a' b')) :
    Quot r → Quot r' → Type :=
  fun q q' => PLift (∃ a a', Quot.mk r a = q ∧ Quot.mk r' a' = q' ∧ Nonempty (RA a a'))

/-- `Quot.mk r a` relates to `Quot.mk r' a'` whenever the representatives are `RA`-related. The `Quot.mk`
    term primitive. -/
@[trocq] def QuotMkR (A A' : Type) (RA : A → A' → Type) (r : A → A → Prop) (r' : A' → A' → Prop)
    (rR : (a : A) → (a' : A') → RA a a' → (b : A) → (b' : A') → RA b b' → PLift (r a b ↔ r' a' b'))
    (a : A) (a' : A') (aRel : RA a a') :
    QuotRel A A' RA r r' rR (Quot.mk r a) (Quot.mk r' a') :=
  PLift.up ⟨a, a', rfl, rfl, ⟨aRel⟩⟩

/- ===================== the graded relator (domain-only variance) =====================
   Only the base `A` is graded (`r`/`r'` are a term argument, `rR` its ungraded relatedness). The relation is a
   `Prop`-truncated subsingleton, so `rInMapK` is `rfl` for free (no class-4 on `pa`). But the forward map uses
   `pa.cov.mapInR` (2a) at every class ≥ 1, so wanting completeness (2b) forces `pa` to `map3`. -/

/-- per-map-class minimal domain class for `Quot` (map needs 2a everywhere; completeness forces map3). -/
def mapQuotVariance : MapClass → ParamClass
  | map0  => (map0,  map0)
  | map1  => (map2a, map0)
  | map2a => (map2a, map0)
  | map2b => (map3,  map0)
  | map3  => (map3,  map0)
  | map4  => (map3,  map0)

/-- minimal domain class to build `Quot` at output class `c` (cov joined with negated contra). -/
def quotVariance (c : ParamClass) : ParamClass := ParamClass.variance mapQuotVariance c

/- The shared cov obligations, written once via the raw `pa.cov` fields + the ungraded `rR`. -/
noncomputable def quotFwdMap {A A' : Type} {RA : A → A' → Type} (r : A → A → Prop) (r' : A' → A' → Prop)
    (mapA : A → A') (mapAInR : ∀ a a', mapA a = a' → RA a a')
    (rR : ∀ a a', RA a a' → ∀ b b', RA b b' → PLift (r a b ↔ r' a' b')) : Quot r → Quot r' :=
  Quot.lift (fun a => Quot.mk r' (mapA a)) (fun a b hab =>
    Quot.sound ((rR a (mapA a) (mapAInR a (mapA a) rfl) b (mapA b) (mapAInR b (mapA b) rfl)).down.mp hab))

noncomputable def quotMapInR {A A' : Type} {RA : A → A' → Type} (r : A → A → Prop) (r' : A' → A' → Prop)
    (mapA : A → A') (mapAInR : ∀ a a', mapA a = a' → RA a a')
    (rR : ∀ a a', RA a a' → ∀ b b', RA b b' → PLift (r a b ↔ r' a' b')) :
    ∀ q q', quotFwdMap r r' mapA mapAInR rR q = q' → QuotRel A A' RA r r' rR q q' :=
  fun q q' h => PLift.up (by
    obtain ⟨a, ha⟩ := q.exists_rep; subst ha
    exact ⟨a, mapA a, rfl, h, ⟨mapAInR a (mapA a) rfl⟩⟩)

theorem quotRInMap {A A' : Type} {RA : A → A' → Type} (r : A → A → Prop) (r' : A' → A' → Prop)
    (mapA : A → A') (mapAInR : ∀ a a', mapA a = a' → RA a a') (mapARInMap : ∀ a a', RA a a' → mapA a = a')
    (rR : ∀ a a', RA a a' → ∀ b b', RA b b' → PLift (r a b ↔ r' a' b')) :
    ∀ q q', QuotRel A A' RA r r' rR q q' → quotFwdMap r r' mapA mapAInR rR q = q' :=
  fun q q' hR => by
    obtain ⟨a, a', ha, ha', ⟨aRel⟩⟩ := hR.down; subst ha; subst ha'
    show Quot.mk r' (mapA a) = Quot.mk r' a'
    rw [mapARInMap a a' aRel]

/-- the covariant half from the domain at `mapQuotVariance m`. Coherence is `rfl` (subsingleton relation). -/
noncomputable def quotCov {A A' : Type} (r : A → A → Prop) (r' : A' → A' → Prop) :
    (m : MapClass) →
    (pa : Param (mapQuotVariance m).1 (mapQuotVariance m).2 A A') →
    (rR : (a : A) → (a' : A') → pa.R a a' → (b : A) → (b' : A') → pa.R b b' → PLift (r a b ↔ r' a' b')) →
    Map m (QuotRel A A' pa.R r r' rR)
  | map0,  _,  _  => {}
  | map1,  pa, rR => { map := quotFwdMap r r' pa.cov.map pa.cov.mapInR rR }
  | map2a, pa, rR => { map := quotFwdMap r r' pa.cov.map pa.cov.mapInR rR,
                       mapInR := quotMapInR r r' pa.cov.map pa.cov.mapInR rR }
  | map2b, pa, rR => { map := quotFwdMap r r' pa.cov.map pa.cov.mapInR rR,
                       rInMap := quotRInMap r r' pa.cov.map pa.cov.mapInR pa.cov.rInMap rR }
  | map3,  pa, rR => { map := quotFwdMap r r' pa.cov.map pa.cov.mapInR rR,
                       mapInR := quotMapInR r r' pa.cov.map pa.cov.mapInR rR,
                       rInMap := quotRInMap r r' pa.cov.map pa.cov.mapInR pa.cov.rInMap rR }
  | map4,  pa, rR => { map := quotFwdMap r r' pa.cov.map pa.cov.mapInR rR,
                       mapInR := quotMapInR r r' pa.cov.map pa.cov.mapInR rR,
                       rInMap := quotRInMap r r' pa.cov.map pa.cov.mapInR pa.cov.rInMap rR,
                       rInMapK := fun _ _ _ => rfl }

/- the contra mirror: A-side uses `pa.contra` (`mapA : A' → A`), maps `Quot r' → Quot r` (`.mpr`). -/
noncomputable def quotBwdMap {A A' : Type} {RA : A → A' → Type} (r : A → A → Prop) (r' : A' → A' → Prop)
    (mapA : A' → A) (mapAInR : ∀ a' a, mapA a' = a → RA a a')
    (rR : ∀ a a', RA a a' → ∀ b b', RA b b' → PLift (r a b ↔ r' a' b')) : Quot r' → Quot r :=
  Quot.lift (fun a' => Quot.mk r (mapA a')) (fun a' b' hab =>
    Quot.sound ((rR (mapA a') a' (mapAInR a' (mapA a') rfl)
                    (mapA b') b' (mapAInR b' (mapA b') rfl)).down.mpr hab))

noncomputable def quotContraMapInR {A A' : Type} {RA : A → A' → Type} (r : A → A → Prop) (r' : A' → A' → Prop)
    (mapA : A' → A) (mapAInR : ∀ a' a, mapA a' = a → RA a a')
    (rR : ∀ a a', RA a a' → ∀ b b', RA b b' → PLift (r a b ↔ r' a' b')) :
    ∀ q' q, quotBwdMap r r' mapA mapAInR rR q' = q → QuotRel A A' RA r r' rR q q' :=
  fun q' q h => PLift.up (by
    obtain ⟨a', ha'⟩ := q'.exists_rep; subst ha'
    exact ⟨mapA a', a', h, rfl, ⟨mapAInR a' (mapA a') rfl⟩⟩)

theorem quotContraRInMap {A A' : Type} {RA : A → A' → Type} (r : A → A → Prop) (r' : A' → A' → Prop)
    (mapA : A' → A) (mapAInR : ∀ a' a, mapA a' = a → RA a a') (mapARInMap : ∀ a' a, RA a a' → mapA a' = a)
    (rR : ∀ a a', RA a a' → ∀ b b', RA b b' → PLift (r a b ↔ r' a' b')) :
    ∀ q' q, QuotRel A A' RA r r' rR q q' → quotBwdMap r r' mapA mapAInR rR q' = q :=
  fun q' q hR => by
    obtain ⟨a, a', ha, ha', ⟨aRel⟩⟩ := hR.down; subst ha; subst ha'
    show Quot.mk r (mapA a') = Quot.mk r a
    rw [mapARInMap a' a aRel]

/-- the contravariant half from the domain's contra at `mapQuotVariance n`. -/
noncomputable def quotContra {A A' : Type} (r : A → A → Prop) (r' : A' → A' → Prop) :
    (n : MapClass) →
    (pa : Param (mapQuotVariance n).2 (mapQuotVariance n).1 A A') →
    (rR : (a : A) → (a' : A') → pa.R a a' → (b : A) → (b' : A') → pa.R b b' → PLift (r a b ↔ r' a' b')) →
    Map n (fun (q' : Quot r') (q : Quot r) => QuotRel A A' pa.R r r' rR q q')
  | map0,  _,  _  => {}
  | map1,  pa, rR => { map := quotBwdMap r r' pa.contra.map pa.contra.mapInR rR }
  | map2a, pa, rR => { map := quotBwdMap r r' pa.contra.map pa.contra.mapInR rR,
                       mapInR := quotContraMapInR r r' pa.contra.map pa.contra.mapInR rR }
  | map2b, pa, rR => { map := quotBwdMap r r' pa.contra.map pa.contra.mapInR rR,
                       rInMap := quotContraRInMap r r' pa.contra.map pa.contra.mapInR pa.contra.rInMap rR }
  | map3,  pa, rR => { map := quotBwdMap r r' pa.contra.map pa.contra.mapInR rR,
                       mapInR := quotContraMapInR r r' pa.contra.map pa.contra.mapInR rR,
                       rInMap := quotContraRInMap r r' pa.contra.map pa.contra.mapInR pa.contra.rInMap rR }
  | map4,  pa, rR => { map := quotBwdMap r r' pa.contra.map pa.contra.mapInR rR,
                       mapInR := quotContraMapInR r r' pa.contra.map pa.contra.mapInR rR,
                       rInMap := quotContraRInMap r r' pa.contra.map pa.contra.mapInR pa.contra.rInMap rR,
                       rInMapK := fun _ _ _ => rfl }

/-- `Quot r ≃ Quot r'` at ANY output class `(m,n)`, domain at the `quotVariance`-minimal class. -/
@[trocq] noncomputable def paramQuot (m n : MapClass) (A A' : Type)
    (pa : Param (quotVariance (m, n)).1 (quotVariance (m, n)).2 A A')
    (r : A → A → Prop) (r' : A' → A' → Prop)
    (rR : (a : A) → (a' : A') → pa.R a a' → (b : A) → (b' : A') → pa.R b b' → PLift (r a b ↔ r' a' b')) :
    Param m n (Quot r) (Quot r') where
  R := QuotRel A A' pa.R r r' rR
  cov := quotCov r r' m (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) rR
  contra := quotContra r r' n (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) rR

end LeTrocq.Lib
