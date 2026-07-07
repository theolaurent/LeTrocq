/-
A registered DEPENDENT parameterized type that is NOT in Lean's prelude: a W-type `WTree`.

The prelude dependent pair `Sigma` ships with the library (`LeTrocq.Lib.Sigma`); this file is the worked
EXAMPLE showing the same type-FAMILY relator machinery applies to a user's own inductive. `WTree A B` is a
well-founded tree — a label `a : A` and `B a`-many subtrees — and like `Sigma` it is parameterized by a type
family `B : A → Type`, handled by `param`'s λ-rule (which turns `B` into the related family `(B', RB)`).

It registers on BOTH surfaces, base-agnostically (the tests instantiate at `Nat ≃ Unary`):
  • the TERM surface (`translate%` / `relate%`, i.e. `⟨·⟩` / `[·]`): the inductive relation `WTreeR` (a TYPE FORMER),
    whose constructor `WTreeR.mk` auto-registers as the `WTree.mk` TERM primitive;
  • the `trocq` / `transfer%` tactic: a `(4,4)` relator `paramWTreeR`, whose family argument `pb` is a whole
    family of `Param`s `∀ a a' (aRel : pa.R a a'), Param … (B a) (B' a')`. The relator proofs are dependent
    (subtrees live over the label), handled by the inductive relation: `cases`/`induction` do the index
    unification, `Subsingleton` identifies the proof slots.
-/
import LeTrocq
namespace LeTrocq.Examples
open LeTrocq LeTrocq.Lib MapClass

/- ===================== a W-type (well-founded trees: a label `a : A` and `B a`-many subtrees) ===================== -/
inductive WTree (A : Type) (B : A → Type) : Type
  | mk (a : A) (f : B a → WTree A B) : WTree A B

/-- two trees are related iff their labels are `RA`-related and, for every related pair of child indices,
    the corresponding subtrees are related. The child-relatedness `fRel` is the W analogue of `ListR.cons`'s
    tail relatedness — here a FUNCTION, since a node has a family of subtrees. -/
@[trocq] inductive WTreeR (A A' : Type) (RA : A → A' → Type) (B : A → Type) (B' : A' → Type)
    (RB : (a : A) → (a' : A') → RA a a' → B a → B' a' → Type) : WTree A B → WTree A' B' → Type
  | mk {a a' f f'} (aRel : RA a a')
      (fRel : (b : B a) → (b' : B' a') → (bRel : RB a a' aRel b b') → WTreeR A A' RA B B' RB (f b) (f' b')) :
      WTreeR A A' RA B B' RB ⟨a, f⟩ ⟨a', f'⟩

/- `WTreeR.mk` auto-registers as the `WTree.mk` term primitive (tagging `WTreeR` derives it via
   `Registry.deriveConstructorPrim`, reordering its `{a a' f f'} aRel fRel` fields into triple form). -/

/-- the relation is a subsingleton when its parts are — by induction on one tree-relatedness (its children
    field is a function into subsingletons, so `funext` + the IH identify it). -/
theorem WTreeR.allEq {A A' : Type} {RA : A → A' → Type} {B : A → Type} {B' : A' → Type}
    {RB : (a : A) → (a' : A') → RA a a' → B a → B' a' → Type}
    (hA : ∀ a a', Subsingleton (RA a a')) (_hB : ∀ a a' aRel b b', Subsingleton (RB a a' aRel b b')) :
    ∀ {s t} (x y : WTreeR A A' RA B B' RB s t), x = y := by
  intro s t x
  induction x with
  | @mk a a' f f' aRel fRel ih =>
    intro y
    cases y with | @mk _ _ _ _ aRel' fRel' =>
      have e : aRel = aRel' := (hA _ _).allEq _ _
      subst e
      have : fRel = fRel' := by
        funext b b' bRel; exact ih b b' bRel (fRel' b b' bRel)
      subst this; rfl

/- ===================== the GRADED relator (variance mechanism, dependent + CONTRAVARIANT family) =========
   `WTree`'s recursive child sits under `B a →`, so the fiber is CONTRAVARIANT: the forward map pulls child
   indices back via `pb.contra`. Hence the whole's soundness (`mapInR`) consumes the family's COMPLETENESS
   (`contra.rInMap`, 2b) and the whole's completeness consumes the family's soundness (2a) — the 2a↔2b swap.
   The domain has the same forall-wrinkle as `Sigma` (2a for map/soundness, map4 for completeness).

   To keep the recursive map class-agnostic (so the completeness `rw`s fire without a `.weaken` in the way),
   `wfwdG`/`wbwdG` take the RAW label map + child transport function, not a `Param`. -/

/-- forward tree map from the raw label map `mapA` and the raw child PULLBACK `mapB` (contravariant fiber). -/
noncomputable def wfwdG {A A' : Type} {B : A → Type} {B' : A' → Type}
    (mapA : A → A') (mapB : (a : A) → B' (mapA a) → B a) : WTree A B → WTree A' B' :=
  fun t => WTree.rec (motive := fun _ => WTree A' B') (fun a _ ih => ⟨mapA a, fun b' => ih (mapB a b')⟩) t

/-- backward tree map from the raw label map `mapA` and the raw child PUSH `mapB`. -/
noncomputable def wbwdG {A A' : Type} {B : A → Type} {B' : A' → Type}
    (mapA : A' → A) (mapB : (a' : A') → B (mapA a') → B' a') : WTree A' B' → WTree A B :=
  fun t => WTree.rec (motive := fun _ => WTree A B) (fun a' _ ih => ⟨mapA a', fun b => ih (mapB a' b)⟩) t

/-- per-map-class minimal `(domain, family)` classes for `WTree` (domain like `Sigma`; family CONTRAVARIANT,
    so its contra slot carries the 2a↔2b-swapped requirement). -/
def mapWTreeVariance : MapClass → ParamClass × ParamClass
  | map0  => ((map0,  map0), (map0, map0))
  | map1  => ((map2a, map0), (map0, map1))
  | map2a => ((map2a, map0), (map0, map2b))
  | map2b => ((map4,  map0), (map0, map2a))
  | map3  => ((map4,  map0), (map0, map3))
  | map4  => ((map4,  map0), (map0, map4))

/-- minimal `(domain, family)` classes to build `WTree` at output class `c`. -/
def wtreeVariance (c : ParamClass) : ParamClass × ParamClass :=
  let (ad, af) := mapWTreeVariance c.1
  let (bd, bf) := mapWTreeVariance c.2
  (ParamClass.join ad (ParamClass.negate bd), ParamClass.join af (ParamClass.negate bf))

/- The shared cov obligations, written ONCE via the family's RAW projected child maps
   (`mapB := fun a a' aRel => (pb a a' aRel).contra.map`, contravariant fiber). `wtreeCovMap` wraps `wfwdG` so
   the `map` field and both proof helpers refer to the same map; the completeness rewrites need `simp only`
   (not `rw`) because the child index is an un-beta-reduced redex. -/
noncomputable def wtreeCovMap {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    (mapA : A → A') (mapAInR : ∀ a a', mapA a = a' → RA a a')
    (mapB : ∀ a a', RA a a' → B' a' → B a) : WTree A B → WTree A' B' :=
  wfwdG mapA (fun a => mapB a (mapA a) (mapAInR a (mapA a) rfl))

noncomputable def wtreeCovMapInR {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    {RB : ∀ a a', RA a a' → B a → B' a' → Type}
    (mapA : A → A') (mapAInR : ∀ a a', mapA a = a' → RA a a')
    (mapB : ∀ a a', RA a a' → B' a' → B a)
    (mapBRInMap : ∀ a a' (aRel : RA a a') b' b, RB a a' aRel b b' → mapB a a' aRel b' = b) :
    ∀ s t, wtreeCovMap mapA mapAInR mapB s = t → WTreeR A A' RA B B' RB s t := by
  intro s _ h
  subst h; induction s with
  | @mk a f ih =>
    refine .mk (mapAInR a (mapA a) rfl) (fun b b' bRel => ?_)
    have hb : mapB a (mapA a) (mapAInR a (mapA a) rfl) b' = b :=
      mapBRInMap a (mapA a) (mapAInR a (mapA a) rfl) b' b bRel
    show WTreeR _ _ _ _ _ _ (f b) (wtreeCovMap mapA mapAInR mapB (f _))
    simp only [hb]; exact ih b

theorem wtreeCovRInMap {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    {RB : ∀ a a', RA a a' → B a → B' a' → Type}
    (mapA : A → A') (mapAInR : ∀ a a', mapA a = a' → RA a a')
    (mapARInMap : ∀ a a', RA a a' → mapA a = a') (mapASub : ∀ a a', Subsingleton (RA a a'))
    (mapB : ∀ a a', RA a a' → B' a' → B a)
    (mapBInR : ∀ a a' (aRel : RA a a') b' b, mapB a a' aRel b' = b → RB a a' aRel b b') :
    ∀ s t, WTreeR A A' RA B B' RB s t → wtreeCovMap mapA mapAInR mapB s = t := by
  intro _ _ r
  induction r with
  | @mk a a' f f' aRel fRel ih =>
    have ha := mapARInMap a a' aRel
    subst ha
    show wtreeCovMap mapA mapAInR mapB ⟨a, f⟩ = ⟨mapA a, f'⟩
    refine congrArg (WTree.mk (mapA a)) ?_
    funext b'
    have hb : mapB a (mapA a) (mapAInR a (mapA a) rfl) b' = mapB a (mapA a) aRel b' := by
      haveI := mapASub a (mapA a)
      rw [Subsingleton.elim (mapAInR a (mapA a) rfl) aRel]
    show wtreeCovMap mapA mapAInR mapB (f _) = f' b'
    simp only [hb]
    exact ih (mapB a (mapA a) aRel b') b' (mapBInR a (mapA a) aRel b' _ rfl)

/-- the covariant half: the map is `wfwdG` of `pa`'s label map and `pb`'s child pullback. -/
noncomputable def wtreeCov {A A' : Type} {B : A → Type} {B' : A' → Type} :
    (m : MapClass) →
    (pa : Param (mapWTreeVariance m).1.1 (mapWTreeVariance m).1.2 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapWTreeVariance m).2.1 (mapWTreeVariance m).2.2 (B a) (B' a')) →
    MapHas m (WTreeR A A' pa.R B B' (fun a a' aRel => (pb a a' aRel).R))
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := wtreeCovMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).contra.map) }
  | map2a, pa, pb => { map := wtreeCovMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).contra.map),
                       mapInR := wtreeCovMapInR pa.cov.map pa.cov.mapInR
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.rInMap) }
  | map2b, pa, pb => { map := wtreeCovMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).contra.map),
                       rInMap := wtreeCovRInMap pa.cov.map pa.cov.mapInR pa.cov.rInMap pa.cov.subsingleton
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.mapInR) }
  | map3,  pa, pb => { map := wtreeCovMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).contra.map),
                       mapInR := wtreeCovMapInR pa.cov.map pa.cov.mapInR
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.rInMap),
                       rInMap := wtreeCovRInMap pa.cov.map pa.cov.mapInR pa.cov.rInMap pa.cov.subsingleton
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.mapInR) }
  | map4,  pa, pb => { map := wtreeCovMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).contra.map),
                       mapInR := wtreeCovMapInR pa.cov.map pa.cov.mapInR
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.rInMap),
                       rInMap := wtreeCovRInMap pa.cov.map pa.cov.mapInR pa.cov.rInMap pa.cov.subsingleton
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.mapInR),
                       rInMapK := fun _ _ _ => WTreeR.allEq (fun a a' => pa.cov.subsingleton a a')
                         (fun a a' aRel b b' => (pb a a' aRel).contra.subsingleton b' b) _ _ }

/- the contra mirror: A-side uses `pa.contra` (`mapA : A' → A`), the fiber uses `pb.cov` (`mapB : … →
   B a → B' a'`), map via `wbwdG`. -/
noncomputable def wtreeContraMap {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    (mapA : A' → A) (mapAInR : ∀ a' a, mapA a' = a → RA a a')
    (mapB : ∀ a a', RA a a' → B a → B' a') : WTree A' B' → WTree A B :=
  wbwdG mapA (fun a' => mapB (mapA a') a' (mapAInR a' (mapA a') rfl))

noncomputable def wtreeContraMapInR {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    {RB : ∀ a a', RA a a' → B a → B' a' → Type}
    (mapA : A' → A) (mapAInR : ∀ a' a, mapA a' = a → RA a a')
    (mapB : ∀ a a', RA a a' → B a → B' a')
    (mapBRInMap : ∀ a a' (aRel : RA a a') b b', RB a a' aRel b b' → mapB a a' aRel b = b') :
    ∀ t s, wtreeContraMap mapA mapAInR mapB t = s → WTreeR A A' RA B B' RB s t := by
  intro t _ h
  subst h; induction t with
  | @mk a' f ih =>
    refine .mk (mapAInR a' (mapA a') rfl) (fun b b' bRel => ?_)
    have hb : mapB (mapA a') a' (mapAInR a' (mapA a') rfl) b = b' :=
      mapBRInMap (mapA a') a' (mapAInR a' (mapA a') rfl) b b' bRel
    show WTreeR _ _ _ _ _ _ (wtreeContraMap mapA mapAInR mapB (f _)) (f b')
    simp only [hb]; exact ih b'

theorem wtreeContraRInMap {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    {RB : ∀ a a', RA a a' → B a → B' a' → Type}
    (mapA : A' → A) (mapAInR : ∀ a' a, mapA a' = a → RA a a')
    (mapARInMap : ∀ a' a, RA a a' → mapA a' = a) (mapASub : ∀ a' a, Subsingleton (RA a a'))
    (mapB : ∀ a a', RA a a' → B a → B' a')
    (mapBInR : ∀ a a' (aRel : RA a a') b b', mapB a a' aRel b = b' → RB a a' aRel b b') :
    ∀ t s, WTreeR A A' RA B B' RB s t → wtreeContraMap mapA mapAInR mapB t = s := by
  intro _ _ r
  induction r with
  | @mk a a' f f' aRel fRel ih =>
    have ha := mapARInMap a' a aRel
    subst ha
    show wtreeContraMap mapA mapAInR mapB ⟨a', f'⟩ = ⟨mapA a', f⟩
    refine congrArg (WTree.mk (mapA a')) ?_
    funext b
    have hb : mapB (mapA a') a' (mapAInR a' (mapA a') rfl) b = mapB (mapA a') a' aRel b := by
      haveI := mapASub a' (mapA a')
      rw [Subsingleton.elim (mapAInR a' (mapA a') rfl) aRel]
    show wtreeContraMap mapA mapAInR mapB (f' _) = f b
    simp only [hb]
    exact ih b (mapB (mapA a') a' aRel b) (mapBInR (mapA a') a' aRel b _ rfl)

/-- the contravariant half: the map is `wbwdG` of `pa`'s (backward) label map and `pb`'s child mapB. -/
noncomputable def wtreeContra {A A' : Type} {B : A → Type} {B' : A' → Type} :
    (n : MapClass) →
    (pa : Param (mapWTreeVariance n).1.2 (mapWTreeVariance n).1.1 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapWTreeVariance n).2.2 (mapWTreeVariance n).2.1 (B a) (B' a')) →
    MapHas n (fun (t : WTree A' B') (s : WTree A B) =>
      WTreeR A A' pa.R B B' (fun a a' aRel => (pb a a' aRel).R) s t)
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := wtreeContraMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).cov.map) }
  | map2a, pa, pb => { map := wtreeContraMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).cov.map),
                       mapInR := wtreeContraMapInR pa.contra.map pa.contra.mapInR
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.rInMap) }
  | map2b, pa, pb => { map := wtreeContraMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).cov.map),
                       rInMap := wtreeContraRInMap pa.contra.map pa.contra.mapInR pa.contra.rInMap pa.contra.subsingleton
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.mapInR) }
  | map3,  pa, pb => { map := wtreeContraMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).cov.map),
                       mapInR := wtreeContraMapInR pa.contra.map pa.contra.mapInR
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.rInMap),
                       rInMap := wtreeContraRInMap pa.contra.map pa.contra.mapInR pa.contra.rInMap pa.contra.subsingleton
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.mapInR) }
  | map4,  pa, pb => { map := wtreeContraMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).cov.map),
                       mapInR := wtreeContraMapInR pa.contra.map pa.contra.mapInR
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.rInMap),
                       rInMap := wtreeContraRInMap pa.contra.map pa.contra.mapInR pa.contra.rInMap pa.contra.subsingleton
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.mapInR),
                       rInMapK := fun _ _ _ => WTreeR.allEq (fun a a' => pa.contra.subsingleton a' a)
                         (fun a a' aRel b b' => (pb a a' aRel).cov.subsingleton b b') _ _ }

/-- `WTree A B ≃ WTree A' B'` at ANY output class `(m,n)`, domain and family at the `wtreeVariance` classes. -/
@[trocq] noncomputable def paramWTree (m n : MapClass) (A A' : Type)
    (pa : Param (wtreeVariance (m, n)).1.1 (wtreeVariance (m, n)).1.2 A A')
    (B : A → Type) (B' : A' → Type)
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (wtreeVariance (m, n)).2.1 (wtreeVariance (m, n)).2.2 (B a) (B' a')) :
    Param m n (WTree A B) (WTree A' B') where
  R := WTreeR A A' pa.R B B' (fun a a' aRel => (pb a a' aRel).R)
  cov := wtreeCov m (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (fun a a' aRel => (pb a a' aRel).weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := wtreeContra n (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (fun a a' aRel => (pb a a' aRel).weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

end LeTrocq.Examples
