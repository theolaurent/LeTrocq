/-
A registered DEPENDENT parameterized type that is NOT in Lean's prelude: a W-type `WTree`.

The prelude dependent pair `Sigma` ships with the library (`LeTrocq.Std.Sigma`); this file is the worked
EXAMPLE showing the same type-FAMILY relator machinery applies to a user's own inductive. `WTree A B` is a
well-founded tree — a label `a : A` and `B a`-many subtrees — and like `Sigma` it is parameterized by a type
family `B : A → Type`, handled by `param`'s λ-rule (which turns `B` into the related family `(B', RB)`).

It registers on BOTH surfaces, base-agnostically (the tests instantiate at `Nat ≃ Unary`):
  • the native TRANSLATION (`translate%` / `relate%`): the inductive relation `WTreeR` (a TYPE FORMER) + the
    constructor `WTreeMkR` as a TERM primitive;
  • the `trocq` / `transfer%` tactic: a `(4,4)` relator `paramWTreeR`, whose family argument `pb` is a whole
    family of `Param`s `∀ a a' (aR : pa.R a a'), Param … (B a) (B' a')`. The relator proofs are dependent
    (subtrees live over the label), handled by the inductive relation: `cases`/`induction` do the index
    unification, `Subsingleton` identifies the proof slots.
-/
import LeTrocq
namespace LeTrocq.Examples
open LeTrocq LeTrocq.Std MapClass

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

/- ===================== the `(4,4)` relator (for the `trocq` / `transfer%` tactic) =====================
   `WTree A B ≃ WTree A' B'` from `pa` and the family `pb`. The forward map is the recursive tree map (each
   node keeps its `pa`-mapped label and recurses on children, whose indices are transported back through
   `pb`'s contra map); completeness is induction on the tree / the `WTreeR` proof, with the child index
   `pb`-round-tripping and proofs identified by `Subsingleton`. -/
section
variable {A A' : Type} (pa : Param map4 map4 A A') {B : A → Type} {B' : A' → Type}
    (pb : (a : A) → (a' : A') → pa.R a a' → Param map4 map4 (B a) (B' a'))

/-- forward tree map: relabel by `pa.cov.map`, recurse on each child after pulling its index back via `pb`. -/
noncomputable def wfwd : WTree A B → WTree A' B' :=
  fun t => WTree.rec (motive := fun _ => WTree A' B')
    (fun a _ ih => ⟨pa.cov.map a,
      fun b' => ih ((pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map b')⟩) t

/-- backward tree map (the same construction read through `pa.contra`/`pb`'s cov). -/
noncomputable def wbwd : WTree A' B' → WTree A B :=
  fun t => WTree.rec (motive := fun _ => WTree A B)
    (fun a' _ ih => ⟨pa.contra.map a',
      fun b => ih ((pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map b)⟩) t

end

@[trocq] noncomputable def paramWTreeR (A A' : Type) (pa : Param map4 map4 A A')
    (B : A → Type) (B' : A' → Type)
    (pb : (a : A) → (a' : A') → pa.R a a' → Param map4 map4 (B a) (B' a')) :
    Param map4 map4 (WTree A B) (WTree A' B') where
  R := WTreeR A A' pa.R B B' (fun a a' aR => (pb a a' aR).R)
  cov :=
    { map := wfwd pa pb
      map_in_R := fun s _ h => by
        subst h
        induction s with
        | @mk a f ih =>
          refine .mk (pa.cov.map_in_R a _ rfl) (fun b b' bR => ?_)
          -- child b' : B' (pa.cov.map a); its pullback equals b, so the recursive subtree matches
          have hb : (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map b' = b := by
            haveI := pa.cov.subsingleton a (pa.cov.map a)
            rw [Subsingleton.elim (pa.cov.map_in_R a (pa.cov.map a) rfl)
              (pa.cov.map_in_R a (pa.cov.map a) rfl)]
            exact (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.R_in_map b' b bR
          show WTreeR _ _ _ _ _ _ (f b) (wfwd pa pb (f _))
          rw [hb]; exact ih b
      R_in_map := fun _ _ r => by
        induction r with
        | @mk a a' f f' aR fR ih =>
          have ha := pa.cov.R_in_map a a' aR
          subst ha
          show wfwd pa pb ⟨a, f⟩ = ⟨pa.cov.map a, f'⟩
          refine congrArg (WTree.mk (pa.cov.map a)) ?_
          funext b'
          have hb : (pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).contra.map b'
              = (pb a (pa.cov.map a) aR).contra.map b' := by
            haveI := pa.cov.subsingleton a (pa.cov.map a)
            rw [Subsingleton.elim (pa.cov.map_in_R a (pa.cov.map a) rfl) aR]
          show wfwd pa pb (f _) = f' b'
          rw [hb]
          exact ih ((pb a (pa.cov.map a) aR).contra.map b') b'
            ((pb a (pa.cov.map a) aR).contra.map_in_R b' _ rfl)
      R_in_mapK := fun _ _ _ => WTreeR.allEq (fun a a' => pa.cov.subsingleton a a')
        (fun a a' aR b b' => (pb a a' aR).cov.subsingleton b b') _ _ }
  contra :=
    { map := wbwd pa pb
      map_in_R := fun t _ h => by
        subst h
        induction t with
        | @mk a' f ih =>
          refine .mk (pa.contra.map_in_R a' _ rfl) (fun b b' bR => ?_)
          have hb : (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map b = b' := by
            exact (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.R_in_map b b' bR
          show WTreeR _ _ _ _ _ _ (wbwd pa pb (f _)) (f b')
          rw [hb]; exact ih b'
      R_in_map := fun _ _ r => by
        induction r with
        | @mk a a' f f' aR fR ih =>
          have ha := pa.contra.R_in_map a' a aR
          subst ha
          show wbwd pa pb ⟨a', f'⟩ = ⟨pa.contra.map a', f⟩
          refine congrArg (WTree.mk (pa.contra.map a')) ?_
          funext b
          have hb : (pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).cov.map b
              = (pb (pa.contra.map a') a' aR).cov.map b := by
            haveI := pa.contra.subsingleton a' (pa.contra.map a')
            rw [Subsingleton.elim (pa.contra.map_in_R a' (pa.contra.map a') rfl) aR]
          show wbwd pa pb (f' _) = f b
          rw [hb]
          exact ih b ((pb (pa.contra.map a') a' aR).cov.map b)
            ((pb (pa.contra.map a') a' aR).cov.map_in_R b _ rfl)
      R_in_mapK := fun _ _ _ => WTreeR.allEq (fun a a' => pa.cov.subsingleton a a')
        (fun a a' aR b b' => (pb a a' aR).cov.subsingleton b b') _ _ }

/- ===================== a family whose domain is NOT the adjacent type argument =====================
   `Tw` carries a phantom type parameter `C` BETWEEN the family's domain `A` and the family `B`. The relator
   framework reads `B`'s domain off its own binder type (`A`, the FIRST type arg), not "the preceding type
   arg" (`C`), so the right witness is used. `Tw A C B` is just `Sigma B`, so its relator IS the standard
   library's `paramSigmaR` (`LeTrocq.Std`). -/
def Tw (A _C : Type) (B : A → Type) : Type := Sigma B

@[trocq] noncomputable def paramTwR (A A' : Type) (pa : Param map4 map4 A A')
    (C C' : Type) (_pc : Param map4 map4 C C') (B : A → Type) (B' : A' → Type)
    (pb : (a : A) → (a' : A') → pa.R a a' → Param map4 map4 (B a) (B' a')) :
    Param map4 map4 (Tw A C B) (Tw A' C' B') := paramSigmaR A A' pa B B' pb

end LeTrocq.Examples
