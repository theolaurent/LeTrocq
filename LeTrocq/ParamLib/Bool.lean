/-
The LeTrocq STANDARD LIBRARY: `Bool`.

A ground (parameter-less) inductive, registered the same way as `List`/`Option` — only with NO type
parameter and two NULLARY constructors. `BoolR` is the parametricity RELATION (the diagonal: `true ~ true`,
`false ~ false`), `BoolTrueR`/`BoolFalseR` are the constructor TERM primitives, and `paramBoolR` is the
`(4,4)` relator. So `Bool` transfers to itself out of the box, on BOTH surfaces — `translate%`/`relate%`
cross `Bool` literals, and `trocq`/`transfer%` cross a `Bool` leaf in a goal.

(A bare reflexive base `Param (4,4) Bool Bool` would serve the solver alone; the inductive relation + the
constructor primitives are what additionally let the term translation `⟨·⟩` rebuild `Bool` VALUES.)
-/
import LeTrocq.Attr
namespace LeTrocq.ParamLib
open LeTrocq MapClass

/-- the parametricity relation of `Bool`: the diagonal (a bool relates only to itself). No parameters, so
    `@[trocq]` classifies it as the `Bool` type former (its two indices are the related objects). -/
@[trocq] inductive BoolR : Bool → Bool → Type
  | tt : BoolR true true
  | ff : BoolR false false

theorem BoolR.allEq : {a b : Bool} → (x y : BoolR a b) → x = y
  | _, _, .tt, .tt => rfl
  | _, _, .ff, .ff => rfl

/-- the two constructors as TERM primitives (relating each literal to itself). -/
@[trocq] def BoolTrueR  : BoolR true true   := .tt
@[trocq] def BoolFalseR : BoolR false false := .ff

/-- `Bool ≃ Bool` at the top class: the identity map, completeness by casing the relation, coherence free
    from `BoolR.allEq` (the diagonal is a subsingleton). -/
@[trocq] noncomputable def paramBoolR : Param map4 map4 Bool Bool where
  R := BoolR
  cov :=
    { map := id
      map_in_R := fun a _ h => by subst h; cases a <;> constructor
      R_in_map := fun _ _ r => by cases r <;> rfl
      R_in_mapK := fun _ _ _ => BoolR.allEq _ _ }
  contra :=
    { map := id
      map_in_R := fun a _ h => by subst h; cases a <;> constructor
      R_in_map := fun _ _ r => by cases r <;> rfl
      R_in_mapK := fun _ _ _ => BoolR.allEq _ _ }

end LeTrocq.ParamLib
