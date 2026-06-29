/-
The LeTrocq STANDARD LIBRARY: `List`.

A type CONSTRUCTOR `List : Type → Type` is a *relator*: its witness lifts a relation on elements to a
relation on lists. Following the standard parametricity translation, that lifted relation is itself an
INDUCTIVE — one constructor per the original's, each carrying the relations of its arguments (`ListR.cons`
pairs an element relation with the tail relation). It registers on BOTH surfaces, each base-agnostic (it
works for ANY element equivalence):

  • the native TRANSLATION (`translate%` / `relate%`): `ListR` is the parametricity RELATION (a TYPE FORMER,
    so `paramType` can cross `List a`), and the constructors `List.nil` / `List.cons` are TERM primitives
    whose relatedness is `ListR.nil` / `ListR.cons`. A list over `A` then rebuilds element-by-element over `B`.

  • the SOLVER / tactic path (`trocq` / `transfer%`): one relator `paramListR`, the `Param` witness sending
    an element equivalence to a `List` equivalence at the top class `(4,4)` (the solver weakens it per use).
    Over the inductive relation the completeness laws are inductions, and the coherence `R_in_mapK` is free
    once the relation is a subsingleton — which it is, since the element relation is (class 4).

This is a USER-LEVEL registration (it could live in a downstream project verbatim); it sits in the library
only because `List` is part of Lean's prelude — exactly like the kernel constants `Quot`/`PUnit`, which are
themselves ordinary `@[trocq]` registrations now (see `LeTrocq.ParamLib.Quot`/`LeTrocq.ParamLib.Unit`).
-/
import LeTrocq.Attr
namespace LeTrocq.ParamLib
open LeTrocq MapClass

/-- two lists are related iff they are cons-by-cons related: same length, corresponding elements `R`-related.
    This is the canonical relational interpretation of the inductive `List`. Its first three parameters
    `(A, A', R)` are what `paramType`'s `mkApp3` supplies; the two list INDICES are read off as the related
    objects, so `@[trocq]` classifies it as the `List` type former. -/
@[trocq] inductive ListR (A A' : Type) (R : A → A' → Type) : List A → List A' → Type
  | nil : ListR A A' R [] []
  | cons {a a' l l'} (aR : R a a') (lR : ListR A A' R l l') : ListR A A' R (a :: l) (a' :: l')

/-- the relation is a subsingleton whenever the element relation is — needed for the `(4,4)` coherence. -/
theorem ListR.allEq {A A' : Type} {R : A → A' → Type} (hR : ∀ a a' (x y : R a a'), x = y) :
    {la : List A} → {lb : List A'} → (x y : ListR A A' R la lb) → x = y
  | _, _, .nil,        .nil          => rfl
  | _, _, .cons aR lR, .cons aR' lR' => by rw [hR _ _ aR aR', ListR.allEq hR lR lR']

/- ===================== the constructors as TERM primitives (for `translate%` / `relate%`) =====================
   In abstraction-theorem triple form `(A,A',R) (a,a',aR) (l,l',lR)`, returning the inductive's constructors;
   the head `List.nil`/`List.cons` on each side is read off the conclusion, so these are term primitives. -/
@[trocq] def ListNilR (A A' : Type) (R : A → A' → Type) : ListR A A' R [] [] := .nil
@[trocq] def ListConsR (A A' : Type) (R : A → A' → Type)
    (a : A) (a' : A') (aR : R a a') (l : List A) (l' : List A') (lR : ListR A A' R l l') :
    ListR A A' R (a :: l) (a' :: l') := .cons aR lR

/- ===================== the `(4,4)` relator (for the `trocq` / `transfer%` tactic) =====================
   `List A ≃ List B` from `A ≃ B`: forward map `List.map`, the two completeness laws by induction (on the
   list / on the `ListR` proof), and the coherence free from `ListR.allEq` + the element subsingleton. -/
@[trocq] noncomputable def paramListR (A B : Type) (pa : Param map4 map4 A B) :
    Param map4 map4 (List A) (List B) where
  R := ListR A B pa.R
  cov :=
    { map := List.map pa.cov.map
      map_in_R := fun la lb h => by
        subst h; induction la with
        | nil => exact .nil
        | cons a l ih => exact .cons (pa.cov.map_in_R a _ rfl) ih
      R_in_map := fun _ _ r => by
        induction r with
        | nil => rfl
        | cons aR lR ih => rw [List.map_cons, pa.cov.R_in_map _ _ aR, ih]
      R_in_mapK := fun _ _ _ => ListR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq) _ _ }
  contra :=
    { map := List.map pa.contra.map
      map_in_R := fun lb la h => by
        subst h; induction lb with
        | nil => exact .nil
        | cons b l ih => exact .cons (pa.contra.map_in_R b _ rfl) ih
      R_in_map := fun _ _ r => by
        induction r with
        | nil => rfl
        | cons aR lR ih => rw [List.map_cons, pa.contra.R_in_map _ _ aR, ih]
      R_in_mapK := fun _ _ _ => ListR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq) _ _ }

end LeTrocq.ParamLib
