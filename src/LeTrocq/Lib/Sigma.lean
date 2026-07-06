/-
The LeTrocq STANDARD LIBRARY: `Sigma` (Σ, the dependent pair).

Beyond `List`/`Option`: `Sigma` is parameterized by a type FAMILY `β : α → Type`. This needs no new machinery
— `param`'s λ-rule turns `B : A → Type` into the RELATED FAMILY `RB : ∀ a a' (aR : RA a a'), B a → B' a' →
Type`, which the inductive relation takes as a parameter. Registers base-agnostically on BOTH surfaces:
  • the TERM surface (`⟨·⟩`/`[·]`): the relation `SigmaR` (a TYPE FORMER) + `SigmaMkR` (a TERM primitive);
  • the tactic path: the GRADED relator `paramSigmaRG`, whose FAMILY argument `β` is a whole family of `Param`s
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
  | mk {a a' b b'} (aR : RA a a') (bR : RB a a' aR b b') : SigmaR A A' RA B B' RB ⟨a, b⟩ ⟨a', b'⟩

@[trocq] def SigmaMkR (A A' : Type) (RA : A → A' → Type) (B : A → Type) (B' : A' → Type)
    (RB : (a : A) → (a' : A') → RA a a' → B a → B' a' → Type)
    (a : A) (a' : A') (aR : RA a a') (b : B a) (b' : B' a') (bR : RB a a' aR b b') :
    SigmaR A A' RA B B' RB ⟨a, b⟩ ⟨a', b'⟩ := .mk aR bR

/-- the relation is a subsingleton when its parts are (the `(4,4)` coherence). `cases`+`subst` handle the
    dependent index, so no `HEq`. -/
theorem SigmaR.allEq {A A' : Type} {RA : A → A' → Type} {B : A → Type} {B' : A' → Type}
    {RB : (a : A) → (a' : A') → RA a a' → B a → B' a' → Type}
    (hA : ∀ a a', Subsingleton (RA a a')) (hB : ∀ a a' aR b b', Subsingleton (RB a a' aR b b'))
    {s : Sigma B} {t : Sigma B'} (x y : SigmaR A A' RA B B' RB s t) : x = y := by
  cases x with | mk aR bR => cases y with | mk aR' bR' =>
    have e : aR = aR' := (hA _ _).allEq _ _
    subst e
    exact congrArg _ ((hB _ _ _ _ _).allEq bR bR')

/- ===================== the GRADED relator (variance mechanism, dependent — parallel to `paramForall`) =====
   `Sigma` is covariant in its DOMAIN `A` and in its FAMILY `β`, but the domain inherits the forall-style
   wrinkle: the forward map already indexes `pb` via `pa.cov.map_in_R` (soundness, 2a), and the completeness
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
   (`bmap`/`bMapInR`/`bRInMap = fun a a' aR => (pb a a' aR).cov.…`), so no `Param` is weakened. -/
noncomputable def sigmaCovMap {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    (amap : A → A') (aMapInR : ∀ a a', amap a = a' → RA a a')
    (bmap : ∀ a a', RA a a' → B a → B' a') : Sigma B → Sigma B' :=
  fun s => ⟨amap s.1, bmap s.1 (amap s.1) (aMapInR s.1 (amap s.1) rfl) s.2⟩

noncomputable def sigmaCovMapInR {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    {pbR : ∀ a a', RA a a' → B a → B' a' → Type}
    (amap : A → A') (aMapInR : ∀ a a', amap a = a' → RA a a')
    (bmap : ∀ a a', RA a a' → B a → B' a')
    (bMapInR : ∀ a a' (aR : RA a a') x y, bmap a a' aR x = y → pbR a a' aR x y) :
    ∀ s t, sigmaCovMap amap aMapInR bmap s = t → SigmaR A A' RA B B' pbR s t := by
  intro s _ h
  obtain ⟨a, b⟩ := s; subst h
  exact .mk (aMapInR a _ rfl) (bMapInR a (amap a) (aMapInR a (amap a) rfl) b _ rfl)

theorem sigmaCovRInMap {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    {pbR : ∀ a a', RA a a' → B a → B' a' → Type}
    (amap : A → A') (aMapInR : ∀ a a', amap a = a' → RA a a')
    (aRInMap : ∀ a a', RA a a' → amap a = a') (aSub : ∀ a a', Subsingleton (RA a a'))
    (bmap : ∀ a a', RA a a' → B a → B' a')
    (bRInMap : ∀ a a' (aR : RA a a') x y, pbR a a' aR x y → bmap a a' aR x = y) :
    ∀ s t, SigmaR A A' RA B B' pbR s t → sigmaCovMap amap aMapInR bmap s = t := by
  intro _ _ r
  cases r with | @mk a a' b b' aR bR =>
    have ha := aRInMap a a' aR
    subst ha
    refine congrArg (Sigma.mk (amap a)) ?_
    haveI := aSub a (amap a)
    rw [Subsingleton.elim (aMapInR a (amap a) rfl) aR]
    exact bRInMap a (amap a) aR b b' bR

/-- the covariant half from the domain at `(mapSigmaVariance m).1` and the family at `(mapSigmaVariance m).2`. -/
noncomputable def sigmaCov {A A' : Type} {B : A → Type} {B' : A' → Type} :
    (m : MapClass) →
    (pa : Param (mapSigmaVariance m).1.1 (mapSigmaVariance m).1.2 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapSigmaVariance m).2.1 (mapSigmaVariance m).2.2 (B a) (B' a')) →
    MapHas m (SigmaR A A' pa.R B B' (fun a a' aR => (pb a a' aR).R))
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := sigmaCovMap pa.cov.map pa.cov.map_in_R (fun a a' aR => (pb a a' aR).cov.map) }
  | map2a, pa, pb => { map := sigmaCovMap pa.cov.map pa.cov.map_in_R (fun a a' aR => (pb a a' aR).cov.map),
                       map_in_R := sigmaCovMapInR pa.cov.map pa.cov.map_in_R
                         (fun a a' aR => (pb a a' aR).cov.map) (fun a a' aR => (pb a a' aR).cov.map_in_R) }
  | map2b, pa, pb => { map := sigmaCovMap pa.cov.map pa.cov.map_in_R (fun a a' aR => (pb a a' aR).cov.map),
                       R_in_map := sigmaCovRInMap pa.cov.map pa.cov.map_in_R pa.cov.R_in_map pa.cov.subsingleton
                         (fun a a' aR => (pb a a' aR).cov.map) (fun a a' aR => (pb a a' aR).cov.R_in_map) }
  | map3,  pa, pb => { map := sigmaCovMap pa.cov.map pa.cov.map_in_R (fun a a' aR => (pb a a' aR).cov.map),
                       map_in_R := sigmaCovMapInR pa.cov.map pa.cov.map_in_R
                         (fun a a' aR => (pb a a' aR).cov.map) (fun a a' aR => (pb a a' aR).cov.map_in_R),
                       R_in_map := sigmaCovRInMap pa.cov.map pa.cov.map_in_R pa.cov.R_in_map pa.cov.subsingleton
                         (fun a a' aR => (pb a a' aR).cov.map) (fun a a' aR => (pb a a' aR).cov.R_in_map) }
  | map4,  pa, pb => { map := sigmaCovMap pa.cov.map pa.cov.map_in_R (fun a a' aR => (pb a a' aR).cov.map),
                       map_in_R := sigmaCovMapInR pa.cov.map pa.cov.map_in_R
                         (fun a a' aR => (pb a a' aR).cov.map) (fun a a' aR => (pb a a' aR).cov.map_in_R),
                       R_in_map := sigmaCovRInMap pa.cov.map pa.cov.map_in_R pa.cov.R_in_map pa.cov.subsingleton
                         (fun a a' aR => (pb a a' aR).cov.map) (fun a a' aR => (pb a a' aR).cov.R_in_map),
                       R_in_mapK := fun _ _ _ => SigmaR.allEq (fun a a' => pa.cov.subsingleton a a')
                         (fun a a' aR b b' => (pb a a' aR).cov.subsingleton b b') _ _ }

/-- the contravariant half. `R_in_mapK` takes the relation's subsingleton from `pa.contra`/`pb.contra`. -/
/- the contra mirror of the cov helpers: A-side uses `pa.contra` (`acMap : A' → A`), the fiber uses
   `pb.contra` (`bmap : … → B' a' → B a`). -/
noncomputable def sigmaContraMap {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    (acMap : A' → A) (acMapInR : ∀ a' a, acMap a' = a → RA a a')
    (bmap : ∀ a a', RA a a' → B' a' → B a) : Sigma B' → Sigma B :=
  fun t => ⟨acMap t.1, bmap (acMap t.1) t.1 (acMapInR t.1 (acMap t.1) rfl) t.2⟩

noncomputable def sigmaContraMapInR {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    {pbR : ∀ a a', RA a a' → B a → B' a' → Type}
    (acMap : A' → A) (acMapInR : ∀ a' a, acMap a' = a → RA a a')
    (bmap : ∀ a a', RA a a' → B' a' → B a)
    (bMapInR : ∀ a a' (aR : RA a a') y x, bmap a a' aR y = x → pbR a a' aR x y) :
    ∀ t s, sigmaContraMap acMap acMapInR bmap t = s → SigmaR A A' RA B B' pbR s t := by
  intro t _ h
  obtain ⟨a', b'⟩ := t; subst h
  exact .mk (acMapInR a' _ rfl) (bMapInR (acMap a') a' (acMapInR a' (acMap a') rfl) b' _ rfl)

theorem sigmaContraRInMap {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    {pbR : ∀ a a', RA a a' → B a → B' a' → Type}
    (acMap : A' → A) (acMapInR : ∀ a' a, acMap a' = a → RA a a')
    (acRInMap : ∀ a' a, RA a a' → acMap a' = a) (acSub : ∀ a' a, Subsingleton (RA a a'))
    (bmap : ∀ a a', RA a a' → B' a' → B a)
    (bRInMap : ∀ a a' (aR : RA a a') y x, pbR a a' aR x y → bmap a a' aR y = x) :
    ∀ t s, SigmaR A A' RA B B' pbR s t → sigmaContraMap acMap acMapInR bmap t = s := by
  intro _ _ r
  cases r with | @mk a a' b b' aR bR =>
    have ha := acRInMap a' a aR
    subst ha
    refine congrArg (Sigma.mk (acMap a')) ?_
    haveI := acSub a' (acMap a')
    rw [Subsingleton.elim (acMapInR a' (acMap a') rfl) aR]
    exact bRInMap (acMap a') a' aR b' b bR

noncomputable def sigmaContra {A A' : Type} {B : A → Type} {B' : A' → Type} :
    (n : MapClass) →
    (pa : Param (mapSigmaVariance n).1.2 (mapSigmaVariance n).1.1 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapSigmaVariance n).2.2 (mapSigmaVariance n).2.1 (B a) (B' a')) →
    MapHas n (fun (t : Sigma B') (s : Sigma B) =>
      SigmaR A A' pa.R B B' (fun a a' aR => (pb a a' aR).R) s t)
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := sigmaContraMap pa.contra.map pa.contra.map_in_R (fun a a' aR => (pb a a' aR).contra.map) }
  | map2a, pa, pb => { map := sigmaContraMap pa.contra.map pa.contra.map_in_R (fun a a' aR => (pb a a' aR).contra.map),
                       map_in_R := sigmaContraMapInR pa.contra.map pa.contra.map_in_R
                         (fun a a' aR => (pb a a' aR).contra.map) (fun a a' aR => (pb a a' aR).contra.map_in_R) }
  | map2b, pa, pb => { map := sigmaContraMap pa.contra.map pa.contra.map_in_R (fun a a' aR => (pb a a' aR).contra.map),
                       R_in_map := sigmaContraRInMap pa.contra.map pa.contra.map_in_R pa.contra.R_in_map pa.contra.subsingleton
                         (fun a a' aR => (pb a a' aR).contra.map) (fun a a' aR => (pb a a' aR).contra.R_in_map) }
  | map3,  pa, pb => { map := sigmaContraMap pa.contra.map pa.contra.map_in_R (fun a a' aR => (pb a a' aR).contra.map),
                       map_in_R := sigmaContraMapInR pa.contra.map pa.contra.map_in_R
                         (fun a a' aR => (pb a a' aR).contra.map) (fun a a' aR => (pb a a' aR).contra.map_in_R),
                       R_in_map := sigmaContraRInMap pa.contra.map pa.contra.map_in_R pa.contra.R_in_map pa.contra.subsingleton
                         (fun a a' aR => (pb a a' aR).contra.map) (fun a a' aR => (pb a a' aR).contra.R_in_map) }
  | map4,  pa, pb => { map := sigmaContraMap pa.contra.map pa.contra.map_in_R (fun a a' aR => (pb a a' aR).contra.map),
                       map_in_R := sigmaContraMapInR pa.contra.map pa.contra.map_in_R
                         (fun a a' aR => (pb a a' aR).contra.map) (fun a a' aR => (pb a a' aR).contra.map_in_R),
                       R_in_map := sigmaContraRInMap pa.contra.map pa.contra.map_in_R pa.contra.R_in_map pa.contra.subsingleton
                         (fun a a' aR => (pb a a' aR).contra.map) (fun a a' aR => (pb a a' aR).contra.R_in_map),
                       R_in_mapK := fun _ _ _ => SigmaR.allEq (fun a a' => pa.contra.subsingleton a' a)
                         (fun a a' aR b b' => (pb a a' aR).contra.subsingleton b' b) _ _ }

/-- `Sigma B ≃ Sigma B'` at ANY output class `(m,n)`, domain and family at the `sigmaVariance`-minimal classes. -/
@[trocq] noncomputable def paramSigmaRG (m n : MapClass) (A A' : Type)
    (pa : Param (sigmaVariance (m, n)).1.1 (sigmaVariance (m, n)).1.2 A A')
    (B : A → Type) (B' : A' → Type)
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (sigmaVariance (m, n)).2.1 (sigmaVariance (m, n)).2.2 (B a) (B' a')) :
    Param m n (Sigma B) (Sigma B') where
  R := SigmaR A A' pa.R B B' (fun a a' aR => (pb a a' aR).R)
  cov := sigmaCov m (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (fun a a' aR => (pb a a' aR).weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := sigmaContra n (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (fun a a' aR => (pb a a' aR).weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

end LeTrocq.Lib
