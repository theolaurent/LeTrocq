/-
A registered DEPENDENT parameterized type that is NOT in Lean's prelude: a W-type `WTree`.

The prelude dependent pair `Sigma` ships with the library (`LeTrocq.Lib.Sigma`); this file is the worked
EXAMPLE showing the same type-FAMILY relator machinery applies to a user's own inductive. `WTree A B` is a
well-founded tree — a label `a : A` and `B a`-many subtrees — and like `Sigma` it is parameterized by a type
family `B : A → Type`, handled by `param`'s λ-rule (which turns `B` into the related family `(B', RB)`).

It registers on BOTH surfaces, base-agnostically (the tests instantiate at `Nat ≃ Unary`):
  • the TERM surface (`translate%` / `relate%`, i.e. `⟨·⟩` / `[·]`): the inductive relation `WTreeR` (a TYPE FORMER) + the
    constructor `WTreeMkR` as a TERM primitive;
  • the `trocq` / `transfer%` tactic: a `(4,4)` relator `paramWTreeR`, whose family argument `pb` is a whole
    family of `Param`s `∀ a a' (aR : pa.R a a'), Param … (B a) (B' a')`. The relator proofs are dependent
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
    the corresponding subtrees are related. The child-relatedness `fR` is the W analogue of `ListR.cons`'s
    tail relatedness — here a FUNCTION, since a node has a family of subtrees. -/
@[trocq] inductive WTreeR (A A' : Type) (RA : A → A' → Type) (B : A → Type) (B' : A' → Type)
    (RB : (a : A) → (a' : A') → RA a a' → B a → B' a' → Type) : WTree A B → WTree A' B' → Type
  | mk {a a' f f'} (aR : RA a a')
      (fR : (b : B a) → (b' : B' a') → (bR : RB a a' aR b b') → WTreeR A A' RA B B' RB (f b) (f' b')) :
      WTreeR A A' RA B B' RB ⟨a, f⟩ ⟨a', f'⟩

@[trocq] def WTreeMkR (A A' : Type) (RA : A → A' → Type) (B : A → Type) (B' : A' → Type)
    (RB : (a : A) → (a' : A') → RA a a' → B a → B' a' → Type)
    (a : A) (a' : A') (aR : RA a a')
    (f : B a → WTree A B) (f' : B' a' → WTree A' B')
    (fR : (b : B a) → (b' : B' a') → (bR : RB a a' aR b b') → WTreeR A A' RA B B' RB (f b) (f' b')) :
    WTreeR A A' RA B B' RB ⟨a, f⟩ ⟨a', f'⟩ := .mk aR fR

/-- the relation is a subsingleton when its parts are — by induction on one tree-relatedness (its children
    field is a function into subsingletons, so `funext` + the IH identify it). -/
theorem WTreeR.allEq {A A' : Type} {RA : A → A' → Type} {B : A → Type} {B' : A' → Type}
    {RB : (a : A) → (a' : A') → RA a a' → B a → B' a' → Type}
    (hA : ∀ a a', Subsingleton (RA a a')) (_hB : ∀ a a' aR b b', Subsingleton (RB a a' aR b b')) :
    ∀ {s t} (x y : WTreeR A A' RA B B' RB s t), x = y := by
  intro s t x
  induction x with
  | @mk a a' f f' aR fR ih =>
    intro y
    cases y with | @mk _ _ _ _ aR' fR' =>
      have e : aR = aR' := (hA _ _).allEq _ _
      subst e
      have : fR = fR' := by
        funext b b' bR; exact ih b b' bR (fR' b b' bR)
      subst this; rfl

/- ===================== the GRADED relator (variance mechanism, dependent + CONTRAVARIANT family) =========
   `WTree`'s recursive child sits under `B a →`, so the fiber is CONTRAVARIANT: the forward map pulls child
   indices back via `pb.contra`. Hence the whole's soundness (`map_in_R`) consumes the family's COMPLETENESS
   (`contra.R_in_map`, 2b) and the whole's completeness consumes the family's soundness (2a) — the 2a↔2b swap.
   The domain has the same forall-wrinkle as `Sigma` (2a for map/soundness, map4 for completeness).

   To keep the recursive map class-agnostic (so the completeness `rw`s fire without a `.weaken` in the way),
   `wfwdG`/`wbwdG` take the RAW label map + child transport function, not a `Param`. -/

/-- forward tree map from the raw label map `lab` and the raw child PULLBACK `pull` (contravariant fiber). -/
noncomputable def wfwdG {A A' : Type} {B : A → Type} {B' : A' → Type}
    (lab : A → A') (pull : (a : A) → B' (lab a) → B a) : WTree A B → WTree A' B' :=
  fun t => WTree.rec (motive := fun _ => WTree A' B') (fun a _ ih => ⟨lab a, fun b' => ih (pull a b')⟩) t

/-- backward tree map from the raw label map `lab` and the raw child PUSH `push`. -/
noncomputable def wbwdG {A A' : Type} {B : A → Type} {B' : A' → Type}
    (lab : A' → A) (push : (a' : A') → B (lab a') → B' a') : WTree A' B' → WTree A B :=
  fun t => WTree.rec (motive := fun _ => WTree A B) (fun a' _ ih => ⟨lab a', fun b => ih (push a' b)⟩) t

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
   (`pullGen := fun a a' aR => (pb a a' aR).contra.map`, contravariant fiber). `wtreeCovMap` wraps `wfwdG` so
   the `map` field and both proof helpers refer to the same map; the completeness rewrites need `simp only`
   (not `rw`) because the child index is an un-beta-reduced redex. -/
noncomputable def wtreeCovMap {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    (lab : A → A') (labMapInR : ∀ a a', lab a = a' → RA a a')
    (pullGen : ∀ a a', RA a a' → B' a' → B a) : WTree A B → WTree A' B' :=
  wfwdG lab (fun a => pullGen a (lab a) (labMapInR a (lab a) rfl))

noncomputable def wtreeCovMapInR {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    {RB : ∀ a a', RA a a' → B a → B' a' → Type}
    (lab : A → A') (labMapInR : ∀ a a', lab a = a' → RA a a')
    (pullGen : ∀ a a', RA a a' → B' a' → B a)
    (pullRInMap : ∀ a a' (aR : RA a a') b' b, RB a a' aR b b' → pullGen a a' aR b' = b) :
    ∀ s t, wtreeCovMap lab labMapInR pullGen s = t → WTreeR A A' RA B B' RB s t := by
  intro s _ h
  subst h; induction s with
  | @mk a f ih =>
    refine .mk (labMapInR a (lab a) rfl) (fun b b' bR => ?_)
    have hb : pullGen a (lab a) (labMapInR a (lab a) rfl) b' = b :=
      pullRInMap a (lab a) (labMapInR a (lab a) rfl) b' b bR
    show WTreeR _ _ _ _ _ _ (f b) (wtreeCovMap lab labMapInR pullGen (f _))
    simp only [hb]; exact ih b

theorem wtreeCovRInMap {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    {RB : ∀ a a', RA a a' → B a → B' a' → Type}
    (lab : A → A') (labMapInR : ∀ a a', lab a = a' → RA a a')
    (labRInMap : ∀ a a', RA a a' → lab a = a') (labSub : ∀ a a', Subsingleton (RA a a'))
    (pullGen : ∀ a a', RA a a' → B' a' → B a)
    (pullMapInR : ∀ a a' (aR : RA a a') b' b, pullGen a a' aR b' = b → RB a a' aR b b') :
    ∀ s t, WTreeR A A' RA B B' RB s t → wtreeCovMap lab labMapInR pullGen s = t := by
  intro _ _ r
  induction r with
  | @mk a a' f f' aR fR ih =>
    have ha := labRInMap a a' aR
    subst ha
    show wtreeCovMap lab labMapInR pullGen ⟨a, f⟩ = ⟨lab a, f'⟩
    refine congrArg (WTree.mk (lab a)) ?_
    funext b'
    have hb : pullGen a (lab a) (labMapInR a (lab a) rfl) b' = pullGen a (lab a) aR b' := by
      haveI := labSub a (lab a)
      rw [Subsingleton.elim (labMapInR a (lab a) rfl) aR]
    show wtreeCovMap lab labMapInR pullGen (f _) = f' b'
    simp only [hb]
    exact ih (pullGen a (lab a) aR b') b' (pullMapInR a (lab a) aR b' _ rfl)

/-- the covariant half: the map is `wfwdG` of `pa`'s label map and `pb`'s child pullback. -/
noncomputable def wtreeCov {A A' : Type} {B : A → Type} {B' : A' → Type} :
    (m : MapClass) →
    (pa : Param (mapWTreeVariance m).1.1 (mapWTreeVariance m).1.2 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapWTreeVariance m).2.1 (mapWTreeVariance m).2.2 (B a) (B' a')) →
    MapHas m (WTreeR A A' pa.R B B' (fun a a' aR => (pb a a' aR).R))
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := wtreeCovMap pa.cov.map pa.cov.map_in_R (fun a a' aR => (pb a a' aR).contra.map) }
  | map2a, pa, pb => { map := wtreeCovMap pa.cov.map pa.cov.map_in_R (fun a a' aR => (pb a a' aR).contra.map),
                       map_in_R := wtreeCovMapInR pa.cov.map pa.cov.map_in_R
                         (fun a a' aR => (pb a a' aR).contra.map) (fun a a' aR => (pb a a' aR).contra.R_in_map) }
  | map2b, pa, pb => { map := wtreeCovMap pa.cov.map pa.cov.map_in_R (fun a a' aR => (pb a a' aR).contra.map),
                       R_in_map := wtreeCovRInMap pa.cov.map pa.cov.map_in_R pa.cov.R_in_map pa.cov.subsingleton
                         (fun a a' aR => (pb a a' aR).contra.map) (fun a a' aR => (pb a a' aR).contra.map_in_R) }
  | map3,  pa, pb => { map := wtreeCovMap pa.cov.map pa.cov.map_in_R (fun a a' aR => (pb a a' aR).contra.map),
                       map_in_R := wtreeCovMapInR pa.cov.map pa.cov.map_in_R
                         (fun a a' aR => (pb a a' aR).contra.map) (fun a a' aR => (pb a a' aR).contra.R_in_map),
                       R_in_map := wtreeCovRInMap pa.cov.map pa.cov.map_in_R pa.cov.R_in_map pa.cov.subsingleton
                         (fun a a' aR => (pb a a' aR).contra.map) (fun a a' aR => (pb a a' aR).contra.map_in_R) }
  | map4,  pa, pb => { map := wtreeCovMap pa.cov.map pa.cov.map_in_R (fun a a' aR => (pb a a' aR).contra.map),
                       map_in_R := wtreeCovMapInR pa.cov.map pa.cov.map_in_R
                         (fun a a' aR => (pb a a' aR).contra.map) (fun a a' aR => (pb a a' aR).contra.R_in_map),
                       R_in_map := wtreeCovRInMap pa.cov.map pa.cov.map_in_R pa.cov.R_in_map pa.cov.subsingleton
                         (fun a a' aR => (pb a a' aR).contra.map) (fun a a' aR => (pb a a' aR).contra.map_in_R),
                       R_in_mapK := fun _ _ _ => WTreeR.allEq (fun a a' => pa.cov.subsingleton a a')
                         (fun a a' aR b b' => (pb a a' aR).contra.subsingleton b' b) _ _ }

/- the contra mirror: A-side uses `pa.contra` (`acMap : A' → A`), the fiber uses `pb.cov` (`pushGen : … →
   B a → B' a'`), map via `wbwdG`. -/
noncomputable def wtreeContraMap {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    (acMap : A' → A) (acMapInR : ∀ a' a, acMap a' = a → RA a a')
    (pushGen : ∀ a a', RA a a' → B a → B' a') : WTree A' B' → WTree A B :=
  wbwdG acMap (fun a' => pushGen (acMap a') a' (acMapInR a' (acMap a') rfl))

noncomputable def wtreeContraMapInR {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    {RB : ∀ a a', RA a a' → B a → B' a' → Type}
    (acMap : A' → A) (acMapInR : ∀ a' a, acMap a' = a → RA a a')
    (pushGen : ∀ a a', RA a a' → B a → B' a')
    (pushRInMap : ∀ a a' (aR : RA a a') b b', RB a a' aR b b' → pushGen a a' aR b = b') :
    ∀ t s, wtreeContraMap acMap acMapInR pushGen t = s → WTreeR A A' RA B B' RB s t := by
  intro t _ h
  subst h; induction t with
  | @mk a' f ih =>
    refine .mk (acMapInR a' (acMap a') rfl) (fun b b' bR => ?_)
    have hb : pushGen (acMap a') a' (acMapInR a' (acMap a') rfl) b = b' :=
      pushRInMap (acMap a') a' (acMapInR a' (acMap a') rfl) b b' bR
    show WTreeR _ _ _ _ _ _ (wtreeContraMap acMap acMapInR pushGen (f _)) (f b')
    simp only [hb]; exact ih b'

theorem wtreeContraRInMap {A A' : Type} {B : A → Type} {B' : A' → Type} {RA : A → A' → Type}
    {RB : ∀ a a', RA a a' → B a → B' a' → Type}
    (acMap : A' → A) (acMapInR : ∀ a' a, acMap a' = a → RA a a')
    (acRInMap : ∀ a' a, RA a a' → acMap a' = a) (acSub : ∀ a' a, Subsingleton (RA a a'))
    (pushGen : ∀ a a', RA a a' → B a → B' a')
    (pushMapInR : ∀ a a' (aR : RA a a') b b', pushGen a a' aR b = b' → RB a a' aR b b') :
    ∀ t s, WTreeR A A' RA B B' RB s t → wtreeContraMap acMap acMapInR pushGen t = s := by
  intro _ _ r
  induction r with
  | @mk a a' f f' aR fR ih =>
    have ha := acRInMap a' a aR
    subst ha
    show wtreeContraMap acMap acMapInR pushGen ⟨a', f'⟩ = ⟨acMap a', f⟩
    refine congrArg (WTree.mk (acMap a')) ?_
    funext b
    have hb : pushGen (acMap a') a' (acMapInR a' (acMap a') rfl) b = pushGen (acMap a') a' aR b := by
      haveI := acSub a' (acMap a')
      rw [Subsingleton.elim (acMapInR a' (acMap a') rfl) aR]
    show wtreeContraMap acMap acMapInR pushGen (f' _) = f b
    simp only [hb]
    exact ih b (pushGen (acMap a') a' aR b) (pushMapInR (acMap a') a' aR b _ rfl)

/-- the contravariant half: the map is `wbwdG` of `pa`'s (backward) label map and `pb`'s child push. -/
noncomputable def wtreeContra {A A' : Type} {B : A → Type} {B' : A' → Type} :
    (n : MapClass) →
    (pa : Param (mapWTreeVariance n).1.2 (mapWTreeVariance n).1.1 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapWTreeVariance n).2.2 (mapWTreeVariance n).2.1 (B a) (B' a')) →
    MapHas n (fun (t : WTree A' B') (s : WTree A B) =>
      WTreeR A A' pa.R B B' (fun a a' aR => (pb a a' aR).R) s t)
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := wtreeContraMap pa.contra.map pa.contra.map_in_R (fun a a' aR => (pb a a' aR).cov.map) }
  | map2a, pa, pb => { map := wtreeContraMap pa.contra.map pa.contra.map_in_R (fun a a' aR => (pb a a' aR).cov.map),
                       map_in_R := wtreeContraMapInR pa.contra.map pa.contra.map_in_R
                         (fun a a' aR => (pb a a' aR).cov.map) (fun a a' aR => (pb a a' aR).cov.R_in_map) }
  | map2b, pa, pb => { map := wtreeContraMap pa.contra.map pa.contra.map_in_R (fun a a' aR => (pb a a' aR).cov.map),
                       R_in_map := wtreeContraRInMap pa.contra.map pa.contra.map_in_R pa.contra.R_in_map pa.contra.subsingleton
                         (fun a a' aR => (pb a a' aR).cov.map) (fun a a' aR => (pb a a' aR).cov.map_in_R) }
  | map3,  pa, pb => { map := wtreeContraMap pa.contra.map pa.contra.map_in_R (fun a a' aR => (pb a a' aR).cov.map),
                       map_in_R := wtreeContraMapInR pa.contra.map pa.contra.map_in_R
                         (fun a a' aR => (pb a a' aR).cov.map) (fun a a' aR => (pb a a' aR).cov.R_in_map),
                       R_in_map := wtreeContraRInMap pa.contra.map pa.contra.map_in_R pa.contra.R_in_map pa.contra.subsingleton
                         (fun a a' aR => (pb a a' aR).cov.map) (fun a a' aR => (pb a a' aR).cov.map_in_R) }
  | map4,  pa, pb => { map := wtreeContraMap pa.contra.map pa.contra.map_in_R (fun a a' aR => (pb a a' aR).cov.map),
                       map_in_R := wtreeContraMapInR pa.contra.map pa.contra.map_in_R
                         (fun a a' aR => (pb a a' aR).cov.map) (fun a a' aR => (pb a a' aR).cov.R_in_map),
                       R_in_map := wtreeContraRInMap pa.contra.map pa.contra.map_in_R pa.contra.R_in_map pa.contra.subsingleton
                         (fun a a' aR => (pb a a' aR).cov.map) (fun a a' aR => (pb a a' aR).cov.map_in_R),
                       R_in_mapK := fun _ _ _ => WTreeR.allEq (fun a a' => pa.contra.subsingleton a' a)
                         (fun a a' aR b b' => (pb a a' aR).cov.subsingleton b b') _ _ }

/-- `WTree A B ≃ WTree A' B'` at ANY output class `(m,n)`, domain and family at the `wtreeVariance` classes. -/
@[trocq] noncomputable def paramWTreeRG (m n : MapClass) (A A' : Type)
    (pa : Param (wtreeVariance (m, n)).1.1 (wtreeVariance (m, n)).1.2 A A')
    (B : A → Type) (B' : A' → Type)
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (wtreeVariance (m, n)).2.1 (wtreeVariance (m, n)).2.2 (B a) (B' a')) :
    Param m n (WTree A B) (WTree A' B') where
  R := WTreeR A A' pa.R B B' (fun a a' aR => (pb a a' aR).R)
  cov := wtreeCov m (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (fun a a' aR => (pb a a' aR).weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := wtreeContra n (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (fun a a' aR => (pb a a' aR).weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

/- ===================== a family whose domain is NOT the adjacent type argument =====================
   `Tw` carries a phantom type parameter `C` BETWEEN the family's domain `A` and the family `B`. The relator
   framework reads `B`'s domain off its own binder type (`A`, the FIRST type arg), not "the preceding type
   arg" (`C`), so the right witness is used. `Tw A C B` is just `Sigma B`, so its relator IS the standard
   library's graded `paramSigmaRG` (`LeTrocq.Lib`), which it delegates to. -/
def Tw (A _C : Type) (B : A → Type) : Type := Sigma B

@[trocq] noncomputable def paramTwR (m n : MapClass) (A A' : Type)
    (pa : Param (sigmaVariance (m, n)).1.1 (sigmaVariance (m, n)).1.2 A A')
    (C C' : Type) (_pc : Param map4 map4 C C') (B : A → Type) (B' : A' → Type)
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (sigmaVariance (m, n)).2.1 (sigmaVariance (m, n)).2.2 (B a) (B' a')) :
    Param m n (Tw A C B) (Tw A' C' B') := paramSigmaRG m n A A' pa B B' pb

end LeTrocq.Examples
