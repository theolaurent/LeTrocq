/-
The LeTrocq STANDARD LIBRARY: `Sigma` (Σ, the dependent pair).

Beyond `List`/`Option`: `Sigma` is parameterized by a type FAMILY `β : α → Type`. This needs no new machinery
— `param`'s λ-rule turns `B : A → Type` into the RELATED FAMILY `RB : ∀ a a' (aRel : RA a a'), B a → B' a' →
Type`, which the inductive relation takes as a parameter. Registers base-agnostically on BOTH surfaces:
  • the TERM surface (`⟨·⟩`/`[·]`): the relation `SigmaR` (a TYPE FORMER) + `SigmaMkR` (a TERM primitive);
  • the tactic path: the GRADED relator `paramSigma`, whose FAMILY argument `β` is a whole family of `Param`s
    (built like `paramForall`'s codomain). Proofs are dependent — `cases`/`induction` unify the index,
    `Subsingleton` identifies the proof slots.

(A non-prelude example with the same family machinery — a W-type — lives in `Examples/WTree`.)
-/
import LeTrocq.Driver.Registry
namespace LeTrocq.Lib
open LeTrocq MapClass

/-- two dependent pairs are related iff their first components are `RA`-related and, OVER that relatedness,
    their second components are `RB`-related. The family relation `RB` is what `param` produces for `β`. -/
@[trocq] inductive SigmaR (A A' : Type) (RA : A → A' → Type) (B : A → Type) (B' : A' → Type)
    (RB : (a : A) → (a' : A') → RA a a' → B a → B' a' → Type) : Sigma B → Sigma B' → Type
  | mk {a a' b b'} (aRel : RA a a') (bRel : RB a a' aRel b b') : SigmaR A A' RA B B' RB ⟨a, b⟩ ⟨a', b'⟩

@[trocq] def SigmaMkR (A A' : Type) (RA : A → A' → Type) (B : A → Type) (B' : A' → Type)
    (RB : (a : A) → (a' : A') → RA a a' → B a → B' a' → Type)
    (a : A) (a' : A') (aRel : RA a a') (b : B a) (b' : B' a') (bRel : RB a a' aRel b b') :
    SigmaR A A' RA B B' RB ⟨a, b⟩ ⟨a', b'⟩ := .mk aRel bRel

/-- the relation is a subsingleton when its parts are (the `(4,4)` coherence). `cases`+`subst` handle the
    dependent index, so no `HEq`. -/
theorem SigmaR.allEq {A A' : Type} {RA : A → A' → Type} {B : A → Type} {B' : A' → Type}
    {RB : (a : A) → (a' : A') → RA a a' → B a → B' a' → Type}
    (hA : ∀ a a', Subsingleton (RA a a')) (hB : ∀ a a' aRel b b', Subsingleton (RB a a' aRel b b'))
    {s : Sigma B} {t : Sigma B'} (x y : SigmaR A A' RA B B' RB s t) : x = y := by
  cases x with | mk aRel bRel => cases y with | mk aRel' bRel' =>
    have e : aRel = aRel' := (hA _ _).allEq _ _
    subst e
    exact congrArg _ ((hB _ _ _ _ _).allEq bRel bRel')

/- ===================== the GRADED relator (variance mechanism, dependent — parallel to `paramForall`) =====
   `Sigma` is covariant in its DOMAIN `A` and in its FAMILY `β`, but the domain inherits the forall-style
   wrinkle: the forward map already indexes `pb` via `pa.cov.mapInR` (soundness, 2a), and the completeness
   fields identify the relatedness proof via `pa.cov.subsingleton` (map4). So the domain needs 2a for the
   map/soundness arms and map4 for the completeness arms; the family tracks the output class (identity). -/

/-- per-map-class minimal `(domain, family)` classes for `Sigma` (domain has the forall wrinkle, family covariant). -/
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

/- The shared cov obligations, written ONCE and reused across the arms via the family's RAW projected maps
   (`mapB`/`mapBInR`/`mapBRInMap = fun a a' aRel => (pb a a' aRel).cov.…`), so no `Param` is weakened. -/
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

/-- the contravariant half. `rInMapK` takes the relation's subsingleton from `pa.contra`/`pb.contra`. -/
/- the contra mirror of the cov helpers: A-side uses `pa.contra` (`mapA : A' → A`), the fiber uses
   `pb.contra` (`mapB : … → B' a' → B a`). -/
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
