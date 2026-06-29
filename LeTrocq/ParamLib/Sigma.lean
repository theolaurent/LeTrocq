/-
The LeTrocq STANDARD LIBRARY: `Sigma` (Σ, the dependent pair).

This goes beyond `List`/`Option`: `Sigma` is parameterized by a type FAMILY `β : α → Type`, not just a type.
That is exactly the case the parametricity translation is built for — and it needs no new machinery, because
`param`'s λ-rule already turns a family argument `B : A → Type` into the RELATED FAMILY `(B', RB)` with
`RB : ∀ a a' (aR : RA a a'), B a → B' a' → Type`. So the inductive parametricity relation just takes that
family relation `RB` as a parameter and uses it in its constructors.

It registers on BOTH surfaces, base-agnostically:
  • the native TRANSLATION (`translate%` / `relate%`): the inductive relation `SigmaR` (a TYPE FORMER) + the
    constructor `SigmaMkR` as a TERM primitive;
  • the `trocq` / `transfer%` tactic: a `(4,4)` relator `paramSigmaR`. The driver's relator framework
    supports a FAMILY argument — the `β`'s relatedness is a whole family of `Param`s
    `∀ a a' (aR : pa.R a a'), Param … (β a) (β' a')` — built like `paramForall`'s codomain. The relator
    proofs are dependent (the second component lives over the first), handled by the inductive relation:
    `cases`/`induction` do the index unification, `Subsingleton` identifies the proof slots.

(A non-prelude dependent example using the same family machinery — a W-type — lives in `Examples/DepParam`.)
-/
import LeTrocq.Attr
namespace LeTrocq.ParamLib
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

end LeTrocq.ParamLib
