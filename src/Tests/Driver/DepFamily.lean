/-
Regression: a dependent type family over a λ-bound TERM, in the term surface (`relate`/`translate`).

`Boxed : Bool → Type` is a singleton former indexed by a Bool value. In `Σ b : Bool, Boxed b` the family body
`Boxed b` mentions the λ-bound `b`, so building the pair's relatedness forces `[·]` to translate `Boxed b`
under the binder `b` — its embedded type pass needs `b`'s relatedness in scope. That works because the one
`senv` is threaded through both halves: the λ rule records `b`'s relatedness, and the type/term passes read it.
-/
import LeTrocq
namespace LeTrocq.Tests
open LeTrocq MapClass LeTrocq.Lib

/- ===================== a Bool-indexed singleton former + its parametricity ===================== -/
inductive Boxed (b : Bool) : Type
  | mk

/-- the parametricity relation of `Boxed`: a singleton (`mk ~ mk`). A type former over the index triple
    `(b, b', bR : PLift (b = b'))` — `Bool` unregistered, so its diagonal relatedness is `PLift (b = b')`. -/
@[trocq] inductive BoxedR (b b' : Bool) (bR : PLift (b = b')) : Boxed b → Boxed b' → Type
  | mk : BoxedR b b' bR Boxed.mk Boxed.mk

/-- `Boxed.mk ↦ Boxed.mk` as a TERM primitive (its index `b` is a term argument). -/
@[trocq] def BoxedMkR (b b' : Bool) (bR : PLift (b = b')) : BoxedR b b' bR Boxed.mk Boxed.mk := .mk

theorem BoxedR.allEq {b b' : Bool} {bR : PLift (b = b')} :
    ∀ {o : Boxed b} {o' : Boxed b'} (x y : BoxedR b b' bR o o'), x = y
  | _, _, .mk, .mk => rfl

/-- the `Boxed b ≃ Boxed b'` relator, trivial since `Boxed` is a singleton (constant maps, subsingleton
    relation). `Boxed` has no gradeable type part, so the graded relator builds `(4,4)` and weakens. -/
noncomputable def paramBoxedR44 (b b' : Bool) (bR : PLift (b = b')) :
    Param map4 map4 (Boxed b) (Boxed b') where
  R := BoxedR b b' bR
  cov :=
    { map := fun _ => Boxed.mk
      mapInR := fun o o' _ => by cases o; cases o'; exact .mk
      rInMap := fun _ _ r => by cases r; rfl
      rInMapK := fun _ _ _ => BoxedR.allEq _ _ }
  contra :=
    { map := fun _ => Boxed.mk
      mapInR := fun o o' _ => by cases o; cases o'; exact .mk
      rInMap := fun _ _ r => by cases r; rfl
      rInMapK := fun _ _ _ => BoxedR.allEq _ _ }

@[trocq] noncomputable def paramBoxedR (m n : MapClass) (b b' : Bool) (bR : PLift (b = b')) :
    Param m n (Boxed b) (Boxed b') :=
  (paramBoxedR44 b b' bR).weaken (MapClass.le_map4 m) (MapClass.le_map4 n)

/- ===================== the regression: the family body `Boxed b` mentions the λ-bound `b` ===================== -/
/-- `relate` builds the pair's relatedness witness, translating `Boxed b` with `b` in scope. Elaborating this
    at all is the test (it threw `unbound variable b` before the fix). -/
noncomputable def depFamilyWit := relate (⟨true, Boxed.mk⟩ : Σ b : Bool, Boxed b)

/-- the same, asserted at its relatedness type. NOTE: under the whole-diagonal short-circuit the entire pair
    is diagonal, so `[·]` collapses it to the generic `PLift (p = p)` rather than descending into a
    `SigmaR`/`BoxedR` witness. The structural family path is instead exercised by the non-diagonal `Σ`/`WTree`
    cases in `Tests.Driver.Tactic` / `Tests.Driver.Counterpart`. -/
example :
    PLift ((⟨true, Boxed.mk⟩ : Σ b : Bool, Boxed b) = ⟨true, Boxed.mk⟩) :=
  relate (⟨true, Boxed.mk⟩ : Σ b : Bool, Boxed b)

/-- `translate` rebuilds the counterpart (the diagonal here) — and it computes. -/
example : (translate (⟨true, Boxed.mk⟩ : Σ b : Bool, Boxed b)) = ⟨true, Boxed.mk⟩ := rfl

/- ===================== a dependent type over a λ-bound TYPE variable ===================== -/
/-- the demand-driven pass also handles a type mentioning a λ-bound TYPE variable: here `List A` under the
    binder `A`. `A`'s `(4,4)` witness sits in the one `senv` (the λ rule records every binder), and the leaf
    rule reads it — so `relate`/`translate` build with no separate seeding. -/
noncomputable def tvWit := relate (fun (A : Type) (xs : List A) => xs)
example : (translate (fun (A : Type) (xs : List A) => xs)) = (fun (A : Type) (xs : List A) => xs) := rfl

end LeTrocq.Tests
