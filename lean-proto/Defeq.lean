/-
Open question #4: definitional-equality demands of the indexed encoding.

Trocq's abstraction theorem needs  Rel(p_□^{α,β}) ≡ Param_α  *definitionally*: when a sort `Type`
is translated, the produced witness `w : Param β Type Type` must have `w.R` reduce DEFINITIONALLY
to `Param α`, so a bound `A_R : w.R A A'` is usable as `A_R : Param α A A'` with no cast.

FINDINGS surfaced while building the encoding (documented here, tested below):

(F1) Lean 4 has NO general universe cumulativity (unlike Coq). The six map-levels genuinely live
     at different universes: levels {0,1,2b} carry only `map : A→B` (data) plus Prop fields, so they
     sit in `Type u`; levels {2a,3,4} carry `map_in_R : ∀ a b, map a = b → R a b` whose codomain is
     `R a b : Type v`, so they sit in `Type (max u v)`. A function `MapHas : MapClass → … → Type ?`
     must therefore pick the join `Type (max u v)` and `ULift` the three small levels.

(F2) `Σ`/`×` (Sigma/Prod) are Type-valued and refuse Prop components (`R_in_map`'s body is an `Eq`,
     i.e. Prop). So the per-level bundles must be `structure`s (which mix Type/Prop fields freely),
     not Σ-towers. Upshot: index over SIX named structures, not 36 — we still avoid Trocq's codegen,
     AND we keep named projections (good for error messages; bears on open question #1).

Core Lean only; no Mathlib.
-/

universe u v

namespace TrocqProto

inductive MapClass | mZero | mOne | mTwoA | mTwoB | mThree | mFour
deriving DecidableEq, Repr

abbrev ParamClass := MapClass × MapClass

/- ## The six map-levels as named structures (Type/Prop mixing is fine in a structure) -/
structure Map0Has {A B : Type u} (_R : A → B → Type v) : Type u where
structure Map1Has {A B : Type u} (_R : A → B → Type v) : Type u where
  map : A → B
structure Map2aHas {A B : Type u} (R : A → B → Type v) where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
structure Map2bHas {A B : Type u} (R : A → B → Type v) : Type u where
  map : A → B
  R_in_map : ∀ a b, R a b → map a = b
structure Map3Has {A B : Type u} (R : A → B → Type v) where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
  R_in_map : ∀ a b, R a b → map a = b
structure Map4Has {A B : Type u} (R : A → B → Type v) where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
  R_in_map : ∀ a b, R a b → map a = b
  R_in_mapK : ∀ a b r, map_in_R a b (R_in_map a b r) = r

/-- The class-indexed bundle. ULift pads the three "small" levels up to `Type (max u v)`. -/
def MapHas : MapClass → {A B : Type u} → (A → B → Type v) → Type (max u v)
  | .mZero,  _, _, R => ULift.{v} (Map0Has R)
  | .mOne,   _, _, R => ULift.{v} (Map1Has R)
  | .mTwoA,  _, _, R => Map2aHas R
  | .mTwoB,  _, _, R => ULift.{v} (Map2bHas R)
  | .mThree, _, _, R => Map3Has R
  | .mFour,  _, _, R => Map4Has R

structure Param (m n : MapClass) (A B : Type u) where
  R      : A → B → Type v
  cov    : MapHas m R
  contra : MapHas n (fun b a => R a b)

/- =========================================================================================
   TEST A: `MapHas` reduces by `rfl` on each literal class.
   ========================================================================================= -/
section A
variable {A B : Type u} (R : A → B → Type v)
example : MapHas .mZero  R = ULift (Map0Has R) := rfl
example : MapHas .mOne   R = ULift (Map1Has R) := rfl
example : MapHas .mTwoA  R = Map2aHas R        := rfl
example : MapHas .mFour  R = Map4Has R         := rfl
end A

/- =========================================================================================
   TEST B (CRITICAL): universe combinator at axiom-free output class β=(0,0), relation = `Param α`.
   Need `(Param_Type ..).R ≡ Param α` definitionally, and usable for typechecking with no cast.
   ========================================================================================= -/
section B
def Param_Type_bot (α : ParamClass) :
    Param.{u+1, max u (v+1)} .mZero .mZero (Type u) (Type u) :=
  { R := fun A B => Param.{u, v} α.1 α.2 A B
    cov := ULift.up {}
    contra := ULift.up {} }

example (α : ParamClass) (A B : Type u) :
    (Param_Type_bot.{u, v} α).R A B = Param.{u, v} α.1 α.2 A B := rfl

-- the abstraction-theorem scenario: A_R typechecks at `Param α A B` by pure defeq, no cast:
example (α : ParamClass) (A B : Type u)
    (AR : (Param_Type_bot.{u, v} α).R A B) : Param.{u, v} α.1 α.2 A B := AR
end B

/- =========================================================================================
   TEST C: named projections through `MapHas` reduce by `rfl` and actually compute.
   ========================================================================================= -/
section C
def Param.map  {A B : Type u} (P : Param.{u, v} .mOne  n A B) : A → B := P.cov.down.map
def Param.mapA {A B : Type u} (P : Param.{u, v} .mTwoA n A B) : A → B := P.cov.map

def funParam {A B : Type u} (f : A → B) : Param.{u, 0} .mOne .mZero A B :=
  { R := fun a b => PLift (f a = b), cov := ULift.up { map := f }, contra := ULift.up {} }

example {A B : Type u} (f : A → B) : (funParam f).map = f := rfl
example : (funParam (fun n : Nat => n + 1)).map 3 = 4 := rfl   -- actually computes
end C

/- =========================================================================================
   TEST D: chained reduction — defeq survives composition (consume the bound A_R, round-trip).
   ========================================================================================= -/
section D
def consume (α : ParamClass) (A A' : Type u)
    (AR : (Param_Type_bot.{u,v} α).R A A') : Param.{u, v} α.1 α.2 A A' := AR

example (α : ParamClass) (A A' : Type u) (p : Param.{u, v} α.1 α.2 A A') :
    consume α A A' p = p := rfl
end D

end TrocqProto
