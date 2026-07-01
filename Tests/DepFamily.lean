/-
Regression test: a DEPENDENT type family over a λ-bound TERM, in the term surface (`relate%`/`translate%`).

`Boxed : Bool → Type` is a singleton former indexed by a Bool VALUE. In `Σ b : Bool, Boxed b` the family
`fun b => Boxed b` has a body `Boxed b` that mentions the λ-bound term `b`. Building the relatedness of such
a pair forces `[·]` (`Transfer.assembleTerm`) to translate `Boxed b` under the binder `b` — i.e. its embedded
type solve (`assembleType`) must have `b`'s relatedness in scope. This previously errored `unbound variable b`
(the embedded solve ran with an empty env); it works once `assembleType` threads the ambient `senv`.

The solver itself already copes: `Boxed`'s index is a TERM argument, which `gen` skips — so only the
assemble side needed the fix. (A family over a λ-bound TYPE variable would additionally need the solver
seeded, and is still unsupported.)
-/
import LeTrocq
namespace LeTrocq.Tests
open LeTrocq MapClass LeTrocq.ParamLib

/- ===================== a Bool-indexed singleton former + its parametricity ===================== -/
inductive Boxed (b : Bool) : Type
  | mk

/-- the parametricity relation of `Boxed`: a singleton (`mk ~ mk`). A TYPE FORMER over the index triple
    `(b, b', bR : BoolR b b')`; the two `Boxed` objects are read off as the related objects. -/
@[trocq] inductive BoxedR (b b' : Bool) (bR : BoolR b b') : Boxed b → Boxed b' → Type
  | mk : BoxedR b b' bR Boxed.mk Boxed.mk

/-- `Boxed.mk ↦ Boxed.mk` as a TERM primitive (its index `b` is a term argument). -/
@[trocq] def BoxedMkR (b b' : Bool) (bR : BoolR b b') : BoxedR b b' bR Boxed.mk Boxed.mk := .mk

theorem BoxedR.allEq {b b' : Bool} {bR : BoolR b b'} :
    ∀ {o : Boxed b} {o' : Boxed b'} (x y : BoxedR b b' bR o o'), x = y
  | _, _, .mk, .mk => rfl

/-- the `(4,4)` relator (for the solver / `transfer%`): `Boxed b ≃ Boxed b'`, trivial since `Boxed` is a
    singleton — every element is `mk`, so both maps are constant and the relation is a subsingleton. -/
@[trocq] noncomputable def paramBoxedR (b b' : Bool) (bR : BoolR b b') :
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

/- ===================== the regression: the family body `Boxed b` mentions the λ-bound `b` ===================== -/
/-- `relate%` builds the relatedness witness of a dependent pair — it must translate `Boxed b` with `b` in
    scope. Elaborating this at all is the test (it threw `unbound variable b` before the fix). -/
noncomputable def depFamilyWit := relate% (⟨true, Boxed.mk⟩ : Σ b : Bool, Boxed b)

/-- the same, asserted at its precise relatedness type (`SigmaR` over the Bool diagonal and `BoxedR`). -/
example :
    SigmaR Bool Bool BoolR (fun b => Boxed b) (fun b => Boxed b) (fun b b' bR => BoxedR b b' bR)
      ⟨true, Boxed.mk⟩ ⟨true, Boxed.mk⟩ :=
  relate% (⟨true, Boxed.mk⟩ : Σ b : Bool, Boxed b)

/-- `translate%` rebuilds the counterpart (the diagonal here) — and it computes. -/
example : (translate% (⟨true, Boxed.mk⟩ : Σ b : Bool, Boxed b)) = ⟨true, Boxed.mk⟩ := rfl

end LeTrocq.Tests
