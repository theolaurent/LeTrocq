/-
Registering a PARAMETERIZED type: `List` (the same recipe applies verbatim to `Option`, at the bottom).

A type CONSTRUCTOR `List : Type → Type` is a *relator*: its witness lifts a relation on elements to a
relation on lists. It registers on BOTH surfaces, each base-agnostic (works for ANY element equivalence;
the tests instantiate at `Nat ≃ Unary`):

  • the SOLVER / tactic path (`trocq` / `transfer%`): one relator `paramListR`, a `Param` witness sending
    an element equivalence to a `List` equivalence. Registered at the top class `(4,4)`; the solver then
    weakens it to whatever class each occurrence of `List _` actually needs.

  • the native TRANSLATION (`translate%` / `relate%`): the parametricity RELATION `ListRel` (a TYPE FORMER,
    so `paramType` can cross `List a`), plus the constructors `List.nil` / `List.cons` as ordinary TERM
    primitives. With those, a literal/recursively-built list over `A` rebuilds element-by-element over `B`.

Only the relator carries real proof; the constructors' relatedness is immediate.
-/
import Trocq
namespace Trocq.Examples
open Trocq MapClass

/- ===================== the parametricity relation of `List` (the TYPE FORMER for `translate%`) =====================
   Two lists are related iff they have the same length and corresponding elements are `R`-related. This is
   the structural relation the native translation uses; `paramListR` below uses the graph relation instead
   (the two surfaces never meet). Its first three args `(A, A', R)` are what `paramType`'s `mkApp3` feeds. -/
@[trocq] def ListRel (A A' : Type) (R : A → A' → Type) : List A → List A' → Type
  | [],     []      => PUnit
  | a :: l, a' :: l' => R a a' × ListRel A A' R l l'
  | _,      _       => PEmpty

/- ===================== the constructors as TERM primitives (for `translate%` / `relate%`) =====================
   In abstraction-theorem triple form `(A,A',R) (a,a',aR) (l,l',lR)`: the head `List.nil`/`List.cons` on each
   side is read off the conclusion, so these classify as ordinary term primitives `List.nil ↦ List.nil`, etc. -/
@[trocq] def ListNilR (A A' : Type) (R : A → A' → Type) : ListRel A A' R [] [] := PUnit.unit
@[trocq] def ListConsR (A A' : Type) (R : A → A' → Type)
    (a : A) (a' : A') (aR : R a a') (l : List A) (l' : List A') (lR : ListRel A A' R l l') :
    ListRel A A' R (a :: l) (a' :: l') := ⟨aR, lR⟩

/- ===================== the `(4,4)` relator (for the `trocq` / `transfer%` tactic) =====================
   `List A ≃ List B` from `A ≃ B`, with the GRAPH relation `la ~ lb ⟺ la.map fwd = lb` (`PLift`-wrapped so
   it is propositional, exactly like the base `RNU`). The forward map is `List.map`; both completeness laws
   are the element laws transported through `List.map_map` and the section/retraction of the base. The
   coherence `R_in_mapK` is free (`PLift` over an equality is a subsingleton). -/
@[trocq] def paramListR (A B : Type) (pa : Param map4 map4 A B) :
    Param map4 map4 (List A) (List B) where
  R := fun la lb => PLift (la.map pa.cov.map = lb)
  cov :=
    { map := (·.map pa.cov.map)
      map_in_R := fun _ _ h => PLift.up h
      R_in_map := fun _ _ r => r.down
      R_in_mapK := fun _ _ _ => rfl }
  contra :=
    { map := (·.map pa.contra.map)
      map_in_R := fun lb la h => PLift.up (by
        -- h : lb.map contra.map = la ; goal : la.map cov.map = lb (the section `cov ∘ contra = id`)
        subst h
        rw [List.map_map, show pa.cov.map ∘ pa.contra.map = id from
              funext fun b => pa.cov.R_in_map _ _ (pa.contra.map_in_R b _ rfl), List.map_id])
      R_in_map := fun lb la r => by
        -- r : la.map cov.map = lb ; goal : lb.map contra.map = la (the retraction `contra ∘ cov = id`)
        have h := r.down; subst h
        rw [List.map_map, show pa.contra.map ∘ pa.cov.map = id from
              funext fun a => pa.contra.R_in_map _ _ (pa.cov.map_in_R a _ rfl), List.map_id]
      R_in_mapK := fun _ _ _ => rfl }

/- ===================== `Option` — the SAME recipe, one constructor pair =====================
   `Option` is a parameterized type too; its registration is identical in shape (relation former + the two
   constructors `none`/`some` + the `(4,4)` relator), just smaller. -/
@[trocq] def OptionRel (A A' : Type) (R : A → A' → Type) : Option A → Option A' → Type
  | none,   none   => PUnit
  | some a, some a' => R a a'
  | _,      _      => PEmpty

@[trocq] def OptionNoneR (A A' : Type) (R : A → A' → Type) : OptionRel A A' R none none := PUnit.unit
@[trocq] def OptionSomeR (A A' : Type) (R : A → A' → Type) (a : A) (a' : A') (aR : R a a') :
    OptionRel A A' R (some a) (some a') := aR

@[trocq] def paramOptionR (A B : Type) (pa : Param map4 map4 A B) :
    Param map4 map4 (Option A) (Option B) where
  R := fun oa ob => PLift (oa.map pa.cov.map = ob)
  cov :=
    { map := (·.map pa.cov.map)
      map_in_R := fun _ _ h => PLift.up h
      R_in_map := fun _ _ r => r.down
      R_in_mapK := fun _ _ _ => rfl }
  contra :=
    { map := (·.map pa.contra.map)
      map_in_R := fun ob oa h => PLift.up (by
        subst h; cases ob <;>
          simp_all [Option.map, pa.cov.R_in_map _ _ (pa.contra.map_in_R _ _ rfl)])
      R_in_map := fun ob oa r => by
        have h := r.down; subst h; cases oa <;>
          simp_all [Option.map, pa.contra.R_in_map _ _ (pa.cov.map_in_R _ _ rfl)]
      R_in_mapK := fun _ _ _ => rfl }

end Trocq.Examples
