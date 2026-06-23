/-
The graded hierarchy + WEAKENING (the ⇓ forget maps).

`Lattice` gave the class algebra; this is the *witness* side: the six `MapKHas` records, the indexed
`MapHas`/`Param`, and the **forgetful coercions** `MapHas src R → MapHas tgt R` whenever `tgt ≤ src`.
A user registers a base at a STRONG class (typically the equivalence `(4,4)`); the solver picks the
MINIMAL class each occurrence needs; the weakening map bridges the two by dropping fields. Proof-light:
every forget is just record projection.

The whole diamond `0 < 1 < {2a,2b} < 3 < 4` is generated from six covering edges
  4 ⟶ 3 ⟶ 2a ⟶ 1 ⟶ 0   and   3 ⟶ 2b ⟶ 1
so `weaken` is their composition along the (unique-up-to-confluence) path.
-/
import Trocq.Lattice
universe u v
namespace Trocq

/- ===================== the six graded records (over `Sort u`, so `Prop` fits too) ===================== -/
-- All six are annotated at the UNIFORM universe `Sort (max u (v+1))`, so `MapHas` is bare (no `ULift`).
-- `A B : Sort u` ⇒ a `Prop` (Sort 0) or a `Type` both work as the related objects (`R` lands in `Type v`).
structure Map0Has {A B : Sort u} (_R : A → B → Type v) : Sort (max u (v+1)) where
structure Map1Has {A B : Sort u} (_R : A → B → Type v) : Sort (max u (v+1)) where
  map : A → B
structure Map2aHas {A B : Sort u} (R : A → B → Type v) : Sort (max u (v+1)) where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
structure Map2bHas {A B : Sort u} (R : A → B → Type v) : Sort (max u (v+1)) where
  map : A → B
  R_in_map : ∀ a b, R a b → map a = b
structure Map3Has {A B : Sort u} (R : A → B → Type v) : Sort (max u (v+1)) where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
  R_in_map : ∀ a b, R a b → map a = b
structure Map4Has {A B : Sort u} (R : A → B → Type v) : Sort (max u (v+1)) where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
  R_in_map : ∀ a b, R a b → map a = b
  R_in_mapK : ∀ a b r, map_in_R a b (R_in_map a b r) = r

/-- the structure a relation carries at a given map-class — all at the uniform `Sort (max u (v+1))`. -/
def MapHas : MapClass → {A B : Sort u} → (A → B → Type v) → Sort (max u (v+1))
  | .map0,  _, _, R => Map0Has R
  | .map1,  _, _, R => Map1Has R
  | .map2a, _, _, R => Map2aHas R
  | .map2b, _, _, R => Map2bHas R
  | .map3,  _, _, R => Map3Has R
  | .map4,  _, _, R => Map4Has R

structure Param (m n : MapClass) (A B : Sort u) where
  R      : A → B → Type v
  cov    : MapHas m R
  contra : MapHas n (fun b a => R a b)

/-- KEY (Lean-specific): a class-4 relation is necessarily a SUBSINGLETON. Two related elements both map
    (via `R_in_map`) to proofs of `map a = b`, which are equal by Lean's proof irrelevance, so `R_in_mapK`
    forces them equal. This is exactly "no univalence ⇒ class 4 = class 3 on h-props" — and it makes the
    `(4,4)` coherence FREE on any relation reachable from class-4 data. -/
theorem Map4Has.subsingleton {A B : Sort u} {R : A → B → Type v} (m : Map4Has R) (a : A) (b : B) :
    Subsingleton (R a b) :=
  ⟨fun r₁ r₂ => by rw [← m.R_in_mapK a b r₁, ← m.R_in_mapK a b r₂]⟩

/-- symmetry: a `Param m n A B` is a `Param n m B A` on the reversed relation (swap cov/contra). -/
def Param.sym {A B : Sort u} {m n : MapClass} (p : Param.{u,v} m n A B) : Param.{u,v} n m B A where
  R := fun b a => p.R a b
  cov := p.contra
  contra := p.cov

/- ===================== the six covering-edge forgets (bare records) ===================== -/
namespace MapClass
variable {A B : Sort u} {R : A → B → Type v}

def e43  (h : Map4Has R)  : Map3Has R  := { map := h.map, map_in_R := h.map_in_R, R_in_map := h.R_in_map }
def e32a (h : Map3Has R)  : Map2aHas R := { map := h.map, map_in_R := h.map_in_R }
def e32b (h : Map3Has R)  : Map2bHas R := { map := h.map, R_in_map := h.R_in_map }
def e2a1 (h : Map2aHas R) : Map1Has R  := { map := h.map }
def e2b1 (h : Map2bHas R) : Map1Has R  := { map := h.map }
def e10  (_ : Map1Has R)  : Map0Has R  := {}

/-- WEAKENING: forget down from `src` to any `tgt ≤ src`. Total via the order proof;
    the `tgt ≰ src` combinations are impossible and discharged by `nomatch`. -/
def weaken : (src tgt : MapClass) → MapClass.le tgt src = true → MapHas src R → MapHas tgt R
  -- src = map4  (m : Map4Has R)
  | .map4, .map4, _, m => m
  | .map4, .map3, _, m => e43 m
  | .map4, .map2a, _, m => e32a (e43 m)
  | .map4, .map2b, _, m => e32b (e43 m)
  | .map4, .map1, _, m => e2a1 (e32a (e43 m))
  | .map4, .map0, _, m => e10 (e2a1 (e32a (e43 m)))
  -- src = map3  (m : Map3Has R)
  | .map3, .map3, _, m => m
  | .map3, .map2a, _, m => e32a m
  | .map3, .map2b, _, m => e32b m
  | .map3, .map1, _, m => e2a1 (e32a m)
  | .map3, .map0, _, m => e10 (e2a1 (e32a m))
  | .map3, .map4, h, _ => nomatch h
  -- src = map2a  (m : Map2aHas R)
  | .map2a, .map2a, _, m => m
  | .map2a, .map1, _, m => e2a1 m
  | .map2a, .map0, _, m => e10 (e2a1 m)
  | .map2a, .map4, h, _ => nomatch h
  | .map2a, .map3, h, _ => nomatch h
  | .map2a, .map2b, h, _ => nomatch h
  -- src = map2b  (m : Map2bHas R)
  | .map2b, .map2b, _, m => m
  | .map2b, .map1, _, m => e2b1 m
  | .map2b, .map0, _, m => e10 (e2b1 m)
  | .map2b, .map4, h, _ => nomatch h
  | .map2b, .map3, h, _ => nomatch h
  | .map2b, .map2a, h, _ => nomatch h
  -- src = map1  (m : Map1Has R)
  | .map1, .map1, _, m => m
  | .map1, .map0, _, m => e10 m
  | .map1, .map4, h, _ => nomatch h
  | .map1, .map3, h, _ => nomatch h
  | .map1, .map2a, h, _ => nomatch h
  | .map1, .map2b, h, _ => nomatch h
  -- src = map0  (m : ULift (Map0Has R))
  | .map0, .map0, _, m => m
  | .map0, .map4, h, _ => nomatch h
  | .map0, .map3, h, _ => nomatch h
  | .map0, .map2a, h, _ => nomatch h
  | .map0, .map2b, h, _ => nomatch h
  | .map0, .map1, h, _ => nomatch h
end MapClass

/- ===================== weakening lifted to `Param` (componentwise) ===================== -/
namespace Param
variable {A B : Sort u}

/-- forget a `Param` down to any componentwise-smaller class pair. -/
def weaken {sm sn tm tn : MapClass}
    (hm : MapClass.le tm sm = true) (hn : MapClass.le tn sn = true)
    (p : Param.{u,v} sm sn A B) : Param.{u,v} tm tn A B where
  R      := p.R
  cov    := MapClass.weaken sm tm hm p.cov
  contra := MapClass.weaken sn tn hn p.contra

/-- the named downgrades a user gets from an equivalence `(4,4)` for free. -/
def toRetraction (p : Param.{u,v} .map4 .map4 A B) : Param.{u,v} .map4 .map2a A B := p.weaken rfl rfl
def toSection    (p : Param.{u,v} .map4 .map4 A B) : Param.{u,v} .map4 .map2b A B := p.weaken rfl rfl
def toFunction   (p : Param.{u,v} .map4 .map4 A B) : Param.{u,v} .map1 .map0  A B := p.weaken rfl rfl
def toRel        (p : Param.{u,v} .map4 .map4 A B) : Param.{u,v} .map0 .map0  A B := p.weaken rfl rfl
end Param

end Trocq
