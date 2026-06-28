/-
Registering DEPENDENT parameterized types: `Sigma` (Σ, the dependent pair) and a W-type `WTree`.

These go beyond `List`/`Option`: they are parameterized by a type FAMILY `β : α → Type`, not just a type.
That is exactly the case the parametricity translation is built for — and it needs no new machinery, because
`param`'s λ-rule already turns a family argument `B : A → Type` into the RELATED FAMILY `(B', RB)` with
`RB : ∀ a a' (aR : RA a a'), B a → B' a' → Type`. So the inductive parametricity relation just takes that
family relation `RB` as a parameter and uses it in its constructors.

Each registers on BOTH surfaces, base-agnostically (the tests instantiate at `Nat ≃ Unary`):
  • the native TRANSLATION (`translate%` / `relate%`): the inductive relation (a TYPE FORMER) + the
    constructor as a TERM primitive;
  • the `trocq` / `transfer%` tactic: a `(4,4)` relator (`paramSigmaR` / `paramWTreeR`). The driver's relator
    framework now supports a FAMILY argument — the `β`'s relatedness is a whole family of `Param`s
    `∀ a a' (aR : pa.R a a'), Param … (β a) (β' a')` — built like `paramForall`'s codomain. The relator
    proofs are dependent (the second component / subtrees live over the first), handled by the inductive
    relation: `cases`/`induction` do the index unification, `Subsingleton` identifies the proof slots.
-/
import Trocq
namespace Trocq.Examples
open Trocq MapClass

/- ===================== `Sigma` (the dependent pair `Σ a, β a`) ===================== -/
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

/- ===================== the `(4,4)` relator (for the `trocq` / `transfer%` tactic) =====================
   `Sigma B ≃ Sigma B'` from the base equivalence `pa` and a FAMILY of equivalences `pb` (one per related
   pair `(a, a')`). The forward map sends `⟨a, b⟩` to `⟨pa.cov.map a, (pb …).cov.map b⟩`; the completeness
   laws `cases` on the inductive `SigmaR` (whose constructor packages the two components with their
   relatednesses), `subst` the first-component equality, and identify the proof slot by `Subsingleton`. -/
@[trocq] noncomputable def paramSigmaR (A A' : Type) (pa : Param map4 map4 A A')
    (B : A → Type) (B' : A' → Type)
    (pb : (a : A) → (a' : A') → pa.R a a' → Param map4 map4 (B a) (B' a')) :
    Param map4 map4 (Sigma B) (Sigma B') where
  R := SigmaR A A' pa.R B B' (fun a a' aR => (pb a a' aR).R)
  cov :=
    { map := fun s => ⟨pa.cov.map s.1, (pb s.1 (pa.cov.map s.1) (pa.cov.map_in_R s.1 _ rfl)).cov.map s.2⟩
      map_in_R := fun s _ h => by
        obtain ⟨a, b⟩ := s; subst h
        exact .mk (pa.cov.map_in_R a _ rfl)
                  ((pb a (pa.cov.map a) (pa.cov.map_in_R a _ rfl)).cov.map_in_R b _ rfl)
      R_in_map := fun _ _ r => by
        cases r with | @mk a a' b b' aR bR =>
          have ha := pa.cov.R_in_map a a' aR
          subst ha
          refine congrArg (Sigma.mk (pa.cov.map a)) ?_
          haveI := pa.cov.subsingleton a (pa.cov.map a)
          rw [Subsingleton.elim (pa.cov.map_in_R a (pa.cov.map a) rfl) aR]
          exact (pb a (pa.cov.map a) aR).cov.R_in_map b b' bR
      R_in_mapK := fun _ _ _ => SigmaR.allEq (fun a a' => pa.cov.subsingleton a a')
        (fun a a' aR b b' => (pb a a' aR).cov.subsingleton b b') _ _ }
  contra :=
    { map := fun s => ⟨pa.contra.map s.1,
        (pb (pa.contra.map s.1) s.1 (pa.contra.map_in_R s.1 _ rfl)).contra.map s.2⟩
      map_in_R := fun t _ h => by
        obtain ⟨a', b'⟩ := t; subst h
        exact .mk (pa.contra.map_in_R a' _ rfl)
                  ((pb (pa.contra.map a') a' (pa.contra.map_in_R a' _ rfl)).contra.map_in_R b' _ rfl)
      R_in_map := fun _ _ r => by
        cases r with | @mk a a' b b' aR bR =>
          have ha := pa.contra.R_in_map a' a aR
          subst ha
          refine congrArg (Sigma.mk (pa.contra.map a')) ?_
          haveI := pa.contra.subsingleton a' (pa.contra.map a')
          rw [Subsingleton.elim (pa.contra.map_in_R a' (pa.contra.map a') rfl) aR]
          exact (pb (pa.contra.map a') a' aR).contra.R_in_map b' b bR
      R_in_mapK := fun _ _ _ => SigmaR.allEq (fun a a' => pa.cov.subsingleton a a')
        (fun a a' aR b b' => (pb a a' aR).cov.subsingleton b b') _ _ }

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
   arg" (`C`), so the right witness is used. `Tw A C B` is just `Sigma B`, so its relator IS `paramSigmaR`. -/
def Tw (A _C : Type) (B : A → Type) : Type := Sigma B

@[trocq] noncomputable def paramTwR (A A' : Type) (pa : Param map4 map4 A A')
    (C C' : Type) (_pc : Param map4 map4 C C') (B : A → Type) (B' : A' → Type)
    (pb : (a : A) → (a' : A') → pa.R a a' → Param map4 map4 (B a) (B' a')) :
    Param map4 map4 (Tw A C B) (Tw A' C' B') := paramSigmaR A A' pa B B' pb

end Trocq.Examples
