/-
`Sigma` (Σ, the dependent pair) — standard-library registration. Parameterized by a type FAMILY `β : α →
Type`: `param`'s λ-rule turns it into a RELATED FAMILY `RB`, which the inductive relation `SigmaR` (a TYPE
FORMER; `SigmaR.mk` auto-registers as the `Sigma.mk` term primitive) takes as a parameter. `paramSigma` is the
graded relator, its FAMILY argument a whole family of `Param`s (like `paramForall`'s codomain).
-/
import LeTrocq.Driver.Registry
namespace LeTrocq.Lib
open LeTrocq MapClass

/-- two dependent pairs are related iff their firsts are `RA`-related and, over that relatedness, their
    seconds are `RB`-related (`RB` is what `param` produces for `β`). The `Sigma` type former. -/
@[trocq] inductive SigmaR (A A' : Type) (RA : A → A' → Type) (B : A → Type) (B' : A' → Type)
    (RB : (a : A) → (a' : A') → RA a a' → B a → B' a' → Type) : Sigma B → Sigma B' → Type
  | mk {a a' b b'} (aRel : RA a a') (bRel : RB a a' aRel b b') : SigmaR A A' RA B B' RB ⟨a, b⟩ ⟨a', b'⟩

/- `SigmaR.mk` auto-registers as the `Sigma.mk` term primitive. -/

/-- the relation is a subsingleton when its parts are — needed for the `(4,4)` coherence. -/
theorem SigmaR.allEq {A A' : Type} {RA : A → A' → Type} {B : A → Type} {B' : A' → Type}
    {RB : (a : A) → (a' : A') → RA a a' → B a → B' a' → Type}
    (hA : ∀ a a', Subsingleton (RA a a')) (hB : ∀ a a' aRel b b', Subsingleton (RB a a' aRel b b'))
    {s : Sigma B} {t : Sigma B'} (x y : SigmaR A A' RA B B' RB s t) : x = y := by
  cases x with | mk aRel bRel => cases y with | mk aRel' bRel' =>
    have e : aRel = aRel' := (hA _ _).allEq _ _
    subst e
    exact congrArg _ ((hB _ _ _ _ _).allEq bRel bRel')

/- ===================== the graded relator (variance parallel to `paramForall`) =====================
   Covariant in domain `A` and family `β`, but the domain inherits the forall wrinkle: the forward map indexes
   `pb` via `pa.cov.mapInR` (2a) and the completeness arms need `pa.cov.subsingleton` (map4). The family tracks
   the output class (identity). -/

/-- per-map-class minimal `(domain, family)` classes for `Sigma`. -/
def mapSigmaVariance : MapClass → ParamClass × ParamClass
  | map0  => ((map0,  map0), (map0,  map0))
  | map1  => ((map2a, map0), (map1,  map0))
  | map2a => ((map2a, map0), (map2a, map0))
  | map2b => ((map4,  map0), (map2b, map0))
  | map3  => ((map4,  map0), (map3,  map0))
  | map4  => ((map4,  map0), (map4,  map0))

/-- minimal `(domain, family)` classes to build `Sigma` at output class `c` (cov joined with negated contra). -/
def sigmaVariance (c : ParamClass) : ParamClass × ParamClass :=
  let (ad, af) := mapSigmaVariance c.1
  let (bd, bf) := mapSigmaVariance c.2
  (ParamClass.join ad (ParamClass.negate bd), ParamClass.join af (ParamClass.negate bf))

/- The shared cov obligations, written once and reused across the arms via the family's raw projected maps
   (`fun a a' aRel => (pb a a' aRel).cov.…`), so no `Param` is weakened. -/
noncomputable def sigmaCovMap {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    (mapA : A → A') (mapAInR : ∀ a a', mapA a = a' → RA a a')
    (mapB : ∀ a a', RA a a' → B a → B' a') : Sigma B → Sigma B' :=
  fun s => ⟨mapA s.1, mapB s.1 (mapA s.1) (mapAInR s.1 (mapA s.1) rfl) s.2⟩

noncomputable def sigmaCovMapInR {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    {famR : ∀ a a', RA a a' → B a → B' a' → Type}
    (mapA : A → A') (mapAInR : ∀ a a', mapA a = a' → RA a a')
    (mapB : ∀ a a', RA a a' → B a → B' a')
    (mapBInR : ∀ a a' (aRel : RA a a') x y, mapB a a' aRel x = y → famR a a' aRel x y) :
    ∀ s t, sigmaCovMap mapA mapAInR mapB s = t → SigmaR A A' RA B B' famR s t := by
  intro s _ h
  obtain ⟨a, b⟩ := s; subst h
  exact .mk (mapAInR a _ rfl) (mapBInR a (mapA a) (mapAInR a (mapA a) rfl) b _ rfl)

theorem sigmaCovRInMap {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    {famR : ∀ a a', RA a a' → B a → B' a' → Type}
    (mapA : A → A') (mapAInR : ∀ a a', mapA a = a' → RA a a')
    (mapARInMap : ∀ a a', RA a a' → mapA a = a') (mapASub : ∀ a a', Subsingleton (RA a a'))
    (mapB : ∀ a a', RA a a' → B a → B' a')
    (mapBRInMap : ∀ a a' (aRel : RA a a') x y, famR a a' aRel x y → mapB a a' aRel x = y) :
    ∀ s t, SigmaR A A' RA B B' famR s t → sigmaCovMap mapA mapAInR mapB s = t := by
  intro _ _ r
  cases r with | @mk a a' b b' aRel bRel =>
    have ha := mapARInMap a a' aRel
    subst ha
    refine congrArg (Sigma.mk (mapA a)) ?_
    haveI := mapASub a (mapA a)
    rw [Subsingleton.elim (mapAInR a (mapA a) rfl) aRel]
    exact mapBRInMap a (mapA a) aRel b b' bRel

/-- the covariant half from the domain at `(mapSigmaVariance m).1` and the family at `(mapSigmaVariance m).2`. -/
noncomputable def sigmaCov {A A' : Type} {B : A → Type} {B' : A' → Type} :
    (m : MapClass) →
    (pa : Param (mapSigmaVariance m).1.1 (mapSigmaVariance m).1.2 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapSigmaVariance m).2.1 (mapSigmaVariance m).2.2 (B a) (B' a')) →
    MapHas m (SigmaR A A' pa.R B B' (fun a a' aRel => (pb a a' aRel).R))
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := sigmaCovMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).cov.map) }
  | map2a, pa, pb => { map := sigmaCovMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).cov.map),
                       mapInR := sigmaCovMapInR pa.cov.map pa.cov.mapInR
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.mapInR) }
  | map2b, pa, pb => { map := sigmaCovMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).cov.map),
                       rInMap := sigmaCovRInMap pa.cov.map pa.cov.mapInR pa.cov.rInMap pa.cov.subsingleton
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.rInMap) }
  | map3,  pa, pb => { map := sigmaCovMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).cov.map),
                       mapInR := sigmaCovMapInR pa.cov.map pa.cov.mapInR
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.mapInR),
                       rInMap := sigmaCovRInMap pa.cov.map pa.cov.mapInR pa.cov.rInMap pa.cov.subsingleton
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.rInMap) }
  | map4,  pa, pb => { map := sigmaCovMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).cov.map),
                       mapInR := sigmaCovMapInR pa.cov.map pa.cov.mapInR
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.mapInR),
                       rInMap := sigmaCovRInMap pa.cov.map pa.cov.mapInR pa.cov.rInMap pa.cov.subsingleton
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.rInMap),
                       rInMapK := fun _ _ _ => SigmaR.allEq (fun a a' => pa.cov.subsingleton a a')
                         (fun a a' aRel b b' => (pb a a' aRel).cov.subsingleton b b') _ _ }

/- the contra mirror of the cov helpers: A-side uses `pa.contra` (`mapA : A' → A`), the fiber `pb.contra`. -/
noncomputable def sigmaContraMap {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    (mapA : A' → A) (mapAInR : ∀ a' a, mapA a' = a → RA a a')
    (mapB : ∀ a a', RA a a' → B' a' → B a) : Sigma B' → Sigma B :=
  fun t => ⟨mapA t.1, mapB (mapA t.1) t.1 (mapAInR t.1 (mapA t.1) rfl) t.2⟩

noncomputable def sigmaContraMapInR {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    {famR : ∀ a a', RA a a' → B a → B' a' → Type}
    (mapA : A' → A) (mapAInR : ∀ a' a, mapA a' = a → RA a a')
    (mapB : ∀ a a', RA a a' → B' a' → B a)
    (mapBInR : ∀ a a' (aRel : RA a a') y x, mapB a a' aRel y = x → famR a a' aRel x y) :
    ∀ t s, sigmaContraMap mapA mapAInR mapB t = s → SigmaR A A' RA B B' famR s t := by
  intro t _ h
  obtain ⟨a', b'⟩ := t; subst h
  exact .mk (mapAInR a' _ rfl) (mapBInR (mapA a') a' (mapAInR a' (mapA a') rfl) b' _ rfl)

theorem sigmaContraRInMap {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    {famR : ∀ a a', RA a a' → B a → B' a' → Type}
    (mapA : A' → A) (mapAInR : ∀ a' a, mapA a' = a → RA a a')
    (mapARInMap : ∀ a' a, RA a a' → mapA a' = a) (mapASub : ∀ a' a, Subsingleton (RA a a'))
    (mapB : ∀ a a', RA a a' → B' a' → B a)
    (mapBRInMap : ∀ a a' (aRel : RA a a') y x, famR a a' aRel x y → mapB a a' aRel y = x) :
    ∀ t s, SigmaR A A' RA B B' famR s t → sigmaContraMap mapA mapAInR mapB t = s := by
  intro _ _ r
  cases r with | @mk a a' b b' aRel bRel =>
    have ha := mapARInMap a' a aRel
    subst ha
    refine congrArg (Sigma.mk (mapA a')) ?_
    haveI := mapASub a' (mapA a')
    rw [Subsingleton.elim (mapAInR a' (mapA a') rfl) aRel]
    exact mapBRInMap (mapA a') a' aRel b' b bRel

noncomputable def sigmaContra {A A' : Type} {B : A → Type} {B' : A' → Type} :
    (n : MapClass) →
    (pa : Param (mapSigmaVariance n).1.2 (mapSigmaVariance n).1.1 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapSigmaVariance n).2.2 (mapSigmaVariance n).2.1 (B a) (B' a')) →
    MapHas n (fun (t : Sigma B') (s : Sigma B) =>
      SigmaR A A' pa.R B B' (fun a a' aRel => (pb a a' aRel).R) s t)
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := sigmaContraMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).contra.map) }
  | map2a, pa, pb => { map := sigmaContraMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).contra.map),
                       mapInR := sigmaContraMapInR pa.contra.map pa.contra.mapInR
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.mapInR) }
  | map2b, pa, pb => { map := sigmaContraMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).contra.map),
                       rInMap := sigmaContraRInMap pa.contra.map pa.contra.mapInR pa.contra.rInMap pa.contra.subsingleton
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.rInMap) }
  | map3,  pa, pb => { map := sigmaContraMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).contra.map),
                       mapInR := sigmaContraMapInR pa.contra.map pa.contra.mapInR
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.mapInR),
                       rInMap := sigmaContraRInMap pa.contra.map pa.contra.mapInR pa.contra.rInMap pa.contra.subsingleton
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.rInMap) }
  | map4,  pa, pb => { map := sigmaContraMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).contra.map),
                       mapInR := sigmaContraMapInR pa.contra.map pa.contra.mapInR
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.mapInR),
                       rInMap := sigmaContraRInMap pa.contra.map pa.contra.mapInR pa.contra.rInMap pa.contra.subsingleton
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.rInMap),
                       rInMapK := fun _ _ _ => SigmaR.allEq (fun a a' => pa.contra.subsingleton a' a)
                         (fun a a' aRel b b' => (pb a a' aRel).contra.subsingleton b' b) _ _ }

/-- `Sigma B ≃ Sigma B'` at ANY output class `(m,n)`, domain and family at the `sigmaVariance`-minimal classes. -/
@[trocq] noncomputable def paramSigma (m n : MapClass) (A A' : Type)
    (pa : Param (sigmaVariance (m, n)).1.1 (sigmaVariance (m, n)).1.2 A A')
    (B : A → Type) (B' : A' → Type)
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (sigmaVariance (m, n)).2.1 (sigmaVariance (m, n)).2.2 (B a) (B' a')) :
    Param m n (Sigma B) (Sigma B') where
  R := SigmaR A A' pa.R B B' (fun a a' aRel => (pb a a' aRel).R)
  cov := sigmaCov m (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (fun a a' aRel => (pb a a' aRel).weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := sigmaContra n (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (fun a a' aRel => (pb a a' aRel).weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

end LeTrocq.Lib
