/-
The LeTrocq STANDARD LIBRARY: `Quot` (the kernel quotient).

`Quot`/`Quot.mk` are kernel constants, but their parametricity registers like any prelude type — NOT a
hardcoded driver primitive. Base-agnostically on BOTH surfaces:
  • the TERM surface (`⟨·⟩`/`[·]`): `QuotRel` is the parametricity RELATION, registered as a TYPE FORMER so
    `⟨·⟩` crosses `Quot r` (counterpart head `Quot ↦ Quot`); `Quot.mk` is a TERM primitive with relatedness `QuotMkR`.
  • the tactic path: the GRADED relator `paramQuot`, from a base equivalence + the relations' correspondence.

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
    A TYPE FORMER keyed by `Quot` (its `(A, A', RA)` and `(r, r', rR)` parameters are supplied by the graded relator `paramQuot`). -/
@[trocq] def QuotRel (A A' : Type) (RA : A → A' → Type) (r : A → A → Prop) (r' : A' → A' → Prop)
    (_rR : (a : A) → (a' : A') → RA a a' → (b : A) → (b' : A') → RA b b' → PLift (r a b ↔ r' a' b')) :
    Quot r → Quot r' → Type :=
  fun q q' => PLift (∃ a a', Quot.mk r a = q ∧ Quot.mk r' a' = q' ∧ Nonempty (RA a a'))

/-- `Quot.mk r a` relates to `Quot.mk r' a'` whenever the representatives are `RA`-related (witness: itself).
    A TERM primitive keyed by `Quot.mk`. -/
@[trocq] def QuotMkR (A A' : Type) (RA : A → A' → Type) (r : A → A → Prop) (r' : A' → A' → Prop)
    (rR : (a : A) → (a' : A') → RA a a' → (b : A) → (b' : A') → RA b b' → PLift (r a b ↔ r' a' b'))
    (a : A) (a' : A') (aRel : RA a a') :
    QuotRel A A' RA r r' rR (Quot.mk r a) (Quot.mk r' a') :=
  PLift.up ⟨a, a', rfl, rfl, ⟨aRel⟩⟩

/- ===================== the GRADED relator (variance mechanism, dependent — domain only) =====================
   Only the base `A` is graded: `r`/`r'` are a TERM argument and `rR` its (ungraded) relatedness. `Quot`'s
   relation is `Prop`-truncated (a `PLift` of an `∃`), so it is ALWAYS a subsingleton — the coherence
   `rInMapK` is `rfl` for FREE, with no class-4 requirement on `pa`. But the forward map's well-definedness
   uses `pa.cov.mapInR` (soundness, 2a) at EVERY class ≥ 1, so an output that wants completeness (`rInMap`,
   2b) forces `pa` to `map3` (both `mapInR` and `rInMap`); `map4` needs no more than `map3` (coherence free). -/

/-- per-map-class minimal DOMAIN class for `Quot` (the map needs 2a everywhere; completeness forces map3). -/
def mapQuotVariance : MapClass → ParamClass
  | map0  => (map0,  map0)
  | map1  => (map2a, map0)
  | map2a => (map2a, map0)
  | map2b => (map3,  map0)
  | map3  => (map3,  map0)
  | map4  => (map3,  map0)

/-- minimal domain class to build `Quot` at output class `c` (cov joined with negated contra). -/
def quotVariance (c : ParamClass) : ParamClass := ParamClass.variance mapQuotVariance c

/- The shared cov obligations, written ONCE via the raw `pa.cov` fields + the (ungraded) `rR`. `QuotRel` is
   a `Prop`-truncated subsingleton, so `mapInR` returns `PLift.up …` (a `def`) and coherence is `rfl`. -/
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
    MapHas m (QuotRel A A' pa.R r r' rR)
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
    MapHas n (fun (q' : Quot r') (q : Quot r) => QuotRel A A' pa.R r r' rR q q')
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
