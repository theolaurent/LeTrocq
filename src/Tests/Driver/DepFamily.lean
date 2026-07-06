/-
Regression test: a DEPENDENT type family over a λ-bound TERM, in the term surface (`relate%`/`translate%`).

`Boxed : Bool → Type` is a singleton former indexed by a Bool VALUE. In `Σ b : Bool, Boxed b` the family
`fun b => Boxed b` has a body `Boxed b` that mentions the λ-bound term `b`. Building the relatedness of such
a pair forces `[·]` (`Transfer.assembleTerm`) to translate `Boxed b` under the binder `b` — i.e. its embedded
type pass (`assembleType`) must have `b`'s relatedness in scope. This works because the ONE `senv` is threaded
through BOTH halves: the λ rule records `b`'s relatedness, and `assembleType`/`assemble` read it. `Boxed`'s
index is a TERM argument — `relatorArgKinds` routes it to the term half, which consumes `b` from `senv`.
-/
import LeTrocq
namespace LeTrocq.Tests
open LeTrocq MapClass LeTrocq.Lib

/- ===================== a Bool-indexed singleton former + its parametricity ===================== -/
inductive Boxed (b : Bool) : Type
  | mk

/-- the parametricity relation of `Boxed`: a singleton (`mk ~ mk`). A TYPE FORMER over the index triple
    `(b, b', bR : PLift (b = b'))` — `Bool` is unregistered, so its diagonal relatedness is `PLift (b = b')`;
    the two `Boxed` objects are read off as the related objects. -/
@[trocq] inductive BoxedR (b b' : Bool) (bR : PLift (b = b')) : Boxed b → Boxed b' → Type
  | mk : BoxedR b b' bR Boxed.mk Boxed.mk

/-- `Boxed.mk ↦ Boxed.mk` as a TERM primitive (its index `b` is a term argument). -/
@[trocq] def BoxedMkR (b b' : Bool) (bR : PLift (b = b')) : BoxedR b b' bR Boxed.mk Boxed.mk := .mk

theorem BoxedR.allEq {b b' : Bool} {bR : PLift (b = b')} :
    ∀ {o : Boxed b} {o' : Boxed b'} (x y : BoxedR b b' bR o o'), x = y
  | _, _, .mk, .mk => rfl

/-- the `Boxed b ≃ Boxed b'` relator, trivial since `Boxed` is a singleton (every element is `mk`, so both
    maps are constant and the relation is a subsingleton). `Boxed` has no gradeable type PART (its index is a
    term argument), so the graded relator builds the `(4,4)` witness and weakens to the demand. -/
noncomputable def paramBoxedR44 (b b' : Bool) (bR : PLift (b = b')) :
    Param map4 map4 (Boxed b) (Boxed b') where
  R := BoxedR b b' bR
  cov :=
    { map := fun _ => Boxed.mk
      map_in_R := fun o o' _ => by cases o; cases o'; exact .mk
      R_in_map := fun _ _ r => by cases r; rfl
      R_in_mapK := fun _ _ _ => BoxedR.allEq _ _ }
  contra :=
    { map := fun _ => Boxed.mk
      map_in_R := fun o o' _ => by cases o; cases o'; exact .mk
      R_in_map := fun _ _ r => by cases r; rfl
      R_in_mapK := fun _ _ _ => BoxedR.allEq _ _ }

@[trocq] noncomputable def paramBoxedR (m n : MapClass) (b b' : Bool) (bR : PLift (b = b')) :
    Param m n (Boxed b) (Boxed b') :=
  (paramBoxedR44 b b' bR).weaken (MapClass.le_map4 m) (MapClass.le_map4 n)

/- ===================== the regression: the family body `Boxed b` mentions the λ-bound `b` ===================== -/
/-- `relate%` builds the relatedness witness of a dependent pair — it must translate `Boxed b` with `b` in
    scope. Elaborating this at all is the test (it threw `unbound variable b` before the fix). -/
noncomputable def depFamilyWit := relate% (⟨true, Boxed.mk⟩ : Σ b : Bool, Boxed b)

/-- the same, asserted at its relatedness type. NOTE: under the WHOLE-DIAGONAL short-circuit the entire pair
    is diagonal (`Bool` and `Boxed` both transfer to themselves), so `[·]` collapses it to the generic
    `PLift (p = p)` rather than descending into a `SigmaR`/`BoxedR` witness. The structural family path (with
    `b`'s relatedness threaded under the binder) is instead exercised by the NON-diagonal `Σ`/`WTree` cases in
    `Tests.Driver.Tactic` / `Tests.Driver.Counterpart` (over `Nat ≃ Unary`), which do not short-circuit. -/
example :
    PLift ((⟨true, Boxed.mk⟩ : Σ b : Bool, Boxed b) = ⟨true, Boxed.mk⟩) :=
  relate% (⟨true, Boxed.mk⟩ : Σ b : Bool, Boxed b)

/-- `translate%` rebuilds the counterpart (the diagonal here) — and it computes. -/
example : (translate% (⟨true, Boxed.mk⟩ : Σ b : Bool, Boxed b)) = ⟨true, Boxed.mk⟩ := rfl

/- ===================== a dependent type over a λ-bound TYPE variable ===================== -/
/-- The demand-driven pass ALSO handles a type mentioning a λ-bound TYPE variable: here `List A` under the
    binder `A`. The old constraint solver errored `gen: unbound fvar` (its embedded `gradeShape` ran with an
    empty binder env); now `A`'s `(4,4)` witness sits in the ONE `senv` (the λ rule records every binder), and
    `assemble`'s leaf rule reads it — so `relate%`/`translate%` build with no separate seeding. -/
noncomputable def tvWit := relate% (fun (A : Type) (xs : List A) => xs)
example : (translate% (fun (A : Type) (xs : List A) => xs)) = (fun (A : Type) (xs : List A) => xs) := rfl

end LeTrocq.Tests
