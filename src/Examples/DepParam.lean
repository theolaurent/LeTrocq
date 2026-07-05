/-
A registered DEPENDENT parameterized type that is NOT in Lean's prelude: a W-type `WTree`.

The prelude dependent pair `Sigma` ships with the library (`LeTrocq.ParamLib.Sigma`); this file is the worked
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
open LeTrocq LeTrocq.ParamLib MapClass

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

/-- the covariant half: the map is `wfwdG` of `pa`'s label map and `pb`'s child pullback. -/
noncomputable def wtreeCov {A A' : Type} {B : A → Type} {B' : A' → Type} :
    (m : MapClass) →
    (pa : Param (mapWTreeVariance m).1.1 (mapWTreeVariance m).1.2 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapWTreeVariance m).2.1 (mapWTreeVariance m).2.2 (B a) (B' a')) →
    MapHas m (WTreeR A A' pa.R B B' (fun a a' aR => (pb a a' aR).R))
  | map0,  _,  _  => {}
  | map1,  pa, pb =>
      { map := wfwdG pa.cov.map (fun a => (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map) }
  | map2a, pa, pb =>
      { map := wfwdG pa.cov.map (fun a => (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map)
        map_in_R := fun s _ h => by
          subst h; induction s with
          | @mk a f ih =>
            refine .mk (pa.cov.map_in_R a _ rfl) (fun b b' bR => ?_)
            have hb : (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map b' = b :=
              (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.R_in_map b' b bR
            show WTreeR _ _ _ _ _ _ (f b)
              (wfwdG pa.cov.map (fun a => (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map) (f _))
            simp only [hb]; exact ih b }
  | map2b, pa, pb =>
      { map := wfwdG pa.cov.map (fun a => (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map)
        R_in_map := fun _ _ r => by
          induction r with
          | @mk a a' f f' aR fR ih =>
            have ha := pa.cov.R_in_map a a' aR
            subst ha
            show wfwdG pa.cov.map (fun a => (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map) ⟨a, f⟩
              = ⟨pa.cov.map a, f'⟩
            refine congrArg (WTree.mk (pa.cov.map a)) ?_
            funext b'
            have hb : (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map b'
                = (pb a (pa.cov.map a) aR).contra.map b' := by
              haveI := pa.cov.subsingleton a (pa.cov.map a)
              rw [Subsingleton.elim (pa.cov.map_in_R a (pa.cov.map a) rfl) aR]
            show wfwdG pa.cov.map (fun a => (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map) (f _)
              = f' b'
            simp only [hb]
            exact ih ((pb a (pa.cov.map a) aR).contra.map b') b'
              ((pb a (pa.cov.map a) aR).contra.map_in_R b' _ rfl) }
  | map3,  pa, pb =>
      { map := wfwdG pa.cov.map (fun a => (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map)
        map_in_R := fun s _ h => by
          subst h; induction s with
          | @mk a f ih =>
            refine .mk (pa.cov.map_in_R a _ rfl) (fun b b' bR => ?_)
            have hb : (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map b' = b :=
              (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.R_in_map b' b bR
            show WTreeR _ _ _ _ _ _ (f b)
              (wfwdG pa.cov.map (fun a => (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map) (f _))
            simp only [hb]; exact ih b
        R_in_map := fun _ _ r => by
          induction r with
          | @mk a a' f f' aR fR ih =>
            have ha := pa.cov.R_in_map a a' aR
            subst ha
            show wfwdG pa.cov.map (fun a => (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map) ⟨a, f⟩
              = ⟨pa.cov.map a, f'⟩
            refine congrArg (WTree.mk (pa.cov.map a)) ?_
            funext b'
            have hb : (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map b'
                = (pb a (pa.cov.map a) aR).contra.map b' := by
              haveI := pa.cov.subsingleton a (pa.cov.map a)
              rw [Subsingleton.elim (pa.cov.map_in_R a (pa.cov.map a) rfl) aR]
            show wfwdG pa.cov.map (fun a => (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map) (f _)
              = f' b'
            simp only [hb]
            exact ih ((pb a (pa.cov.map a) aR).contra.map b') b'
              ((pb a (pa.cov.map a) aR).contra.map_in_R b' _ rfl) }
  | map4,  pa, pb =>
      { map := wfwdG pa.cov.map (fun a => (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map)
        map_in_R := fun s _ h => by
          subst h; induction s with
          | @mk a f ih =>
            refine .mk (pa.cov.map_in_R a _ rfl) (fun b b' bR => ?_)
            have hb : (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map b' = b :=
              (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.R_in_map b' b bR
            show WTreeR _ _ _ _ _ _ (f b)
              (wfwdG pa.cov.map (fun a => (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map) (f _))
            simp only [hb]; exact ih b
        R_in_map := fun _ _ r => by
          induction r with
          | @mk a a' f f' aR fR ih =>
            have ha := pa.cov.R_in_map a a' aR
            subst ha
            show wfwdG pa.cov.map (fun a => (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map) ⟨a, f⟩
              = ⟨pa.cov.map a, f'⟩
            refine congrArg (WTree.mk (pa.cov.map a)) ?_
            funext b'
            have hb : (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map b'
                = (pb a (pa.cov.map a) aR).contra.map b' := by
              haveI := pa.cov.subsingleton a (pa.cov.map a)
              rw [Subsingleton.elim (pa.cov.map_in_R a (pa.cov.map a) rfl) aR]
            show wfwdG pa.cov.map (fun a => (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map) (f _)
              = f' b'
            simp only [hb]
            exact ih ((pb a (pa.cov.map a) aR).contra.map b') b'
              ((pb a (pa.cov.map a) aR).contra.map_in_R b' _ rfl)
        R_in_mapK := fun _ _ _ => WTreeR.allEq (fun a a' => pa.cov.subsingleton a a')
          (fun a a' aR b b' => (pb a a' aR).contra.subsingleton b' b) _ _ }

/-- the contravariant half: the map is `wbwdG` of `pa`'s (backward) label map and `pb`'s child push. -/
noncomputable def wtreeContra {A A' : Type} {B : A → Type} {B' : A' → Type} :
    (n : MapClass) →
    (pa : Param (mapWTreeVariance n).1.2 (mapWTreeVariance n).1.1 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapWTreeVariance n).2.2 (mapWTreeVariance n).2.1 (B a) (B' a')) →
    MapHas n (fun (t : WTree A' B') (s : WTree A B) =>
      WTreeR A A' pa.R B B' (fun a a' aR => (pb a a' aR).R) s t)
  | map0,  _,  _  => {}
  | map1,  pa, pb =>
      { map := wbwdG pa.contra.map
          (fun a' => (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map) }
  | map2a, pa, pb =>
      { map := wbwdG pa.contra.map
          (fun a' => (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map)
        map_in_R := fun t _ h => by
          subst h; induction t with
          | @mk a' f ih =>
            refine .mk (pa.contra.map_in_R a' _ rfl) (fun b b' bR => ?_)
            have hb : (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map b = b' :=
              (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.R_in_map b b' bR
            show WTreeR _ _ _ _ _ _ (wbwdG pa.contra.map
              (fun a' => (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map) (f _)) (f b')
            simp only [hb]; exact ih b' }
  | map2b, pa, pb =>
      { map := wbwdG pa.contra.map
          (fun a' => (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map)
        R_in_map := fun _ _ r => by
          induction r with
          | @mk a a' f f' aR fR ih =>
            have ha := pa.contra.R_in_map a' a aR
            subst ha
            show wbwdG pa.contra.map
              (fun a' => (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map) ⟨a', f'⟩
              = ⟨pa.contra.map a', f⟩
            refine congrArg (WTree.mk (pa.contra.map a')) ?_
            funext b
            have hb : (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map b
                = (pb (pa.contra.map a') a' aR).cov.map b := by
              haveI := pa.contra.subsingleton a' (pa.contra.map a')
              rw [Subsingleton.elim (pa.contra.map_in_R a' (pa.contra.map a') rfl) aR]
            show wbwdG pa.contra.map
              (fun a' => (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map) (f' _) = f b
            simp only [hb]
            exact ih b ((pb (pa.contra.map a') a' aR).cov.map b)
              ((pb (pa.contra.map a') a' aR).cov.map_in_R b _ rfl) }
  | map3,  pa, pb =>
      { map := wbwdG pa.contra.map
          (fun a' => (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map)
        map_in_R := fun t _ h => by
          subst h; induction t with
          | @mk a' f ih =>
            refine .mk (pa.contra.map_in_R a' _ rfl) (fun b b' bR => ?_)
            have hb : (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map b = b' :=
              (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.R_in_map b b' bR
            show WTreeR _ _ _ _ _ _ (wbwdG pa.contra.map
              (fun a' => (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map) (f _)) (f b')
            simp only [hb]; exact ih b'
        R_in_map := fun _ _ r => by
          induction r with
          | @mk a a' f f' aR fR ih =>
            have ha := pa.contra.R_in_map a' a aR
            subst ha
            show wbwdG pa.contra.map
              (fun a' => (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map) ⟨a', f'⟩
              = ⟨pa.contra.map a', f⟩
            refine congrArg (WTree.mk (pa.contra.map a')) ?_
            funext b
            have hb : (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map b
                = (pb (pa.contra.map a') a' aR).cov.map b := by
              haveI := pa.contra.subsingleton a' (pa.contra.map a')
              rw [Subsingleton.elim (pa.contra.map_in_R a' (pa.contra.map a') rfl) aR]
            show wbwdG pa.contra.map
              (fun a' => (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map) (f' _) = f b
            simp only [hb]
            exact ih b ((pb (pa.contra.map a') a' aR).cov.map b)
              ((pb (pa.contra.map a') a' aR).cov.map_in_R b _ rfl) }
  | map4,  pa, pb =>
      { map := wbwdG pa.contra.map
          (fun a' => (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map)
        map_in_R := fun t _ h => by
          subst h; induction t with
          | @mk a' f ih =>
            refine .mk (pa.contra.map_in_R a' _ rfl) (fun b b' bR => ?_)
            have hb : (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map b = b' :=
              (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.R_in_map b b' bR
            show WTreeR _ _ _ _ _ _ (wbwdG pa.contra.map
              (fun a' => (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map) (f _)) (f b')
            simp only [hb]; exact ih b'
        R_in_map := fun _ _ r => by
          induction r with
          | @mk a a' f f' aR fR ih =>
            have ha := pa.contra.R_in_map a' a aR
            subst ha
            show wbwdG pa.contra.map
              (fun a' => (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map) ⟨a', f'⟩
              = ⟨pa.contra.map a', f⟩
            refine congrArg (WTree.mk (pa.contra.map a')) ?_
            funext b
            have hb : (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map b
                = (pb (pa.contra.map a') a' aR).cov.map b := by
              haveI := pa.contra.subsingleton a' (pa.contra.map a')
              rw [Subsingleton.elim (pa.contra.map_in_R a' (pa.contra.map a') rfl) aR]
            show wbwdG pa.contra.map
              (fun a' => (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map) (f' _) = f b
            simp only [hb]
            exact ih b ((pb (pa.contra.map a') a' aR).cov.map b)
              ((pb (pa.contra.map a') a' aR).cov.map_in_R b _ rfl)
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
   library's graded `paramSigmaRG` (`LeTrocq.ParamLib`), which it delegates to. -/
def Tw (A _C : Type) (B : A → Type) : Type := Sigma B

@[trocq] noncomputable def paramTwR (m n : MapClass) (A A' : Type)
    (pa : Param (sigmaVariance (m, n)).1.1 (sigmaVariance (m, n)).1.2 A A')
    (C C' : Type) (_pc : Param map4 map4 C C') (B : A → Type) (B' : A' → Type)
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (sigmaVariance (m, n)).2.1 (sigmaVariance (m, n)).2.2 (B a) (B' a')) :
    Param m n (Tw A C B) (Tw A' C' B') := paramSigmaRG m n A A' pa B B' pb

end LeTrocq.Examples
