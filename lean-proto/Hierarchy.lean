/-
MILESTONE 6, layer 2: the graded hierarchy + WEAKENING (the ⇓ forget maps).

Layer 1 (`Lattice.lean`) gave the class algebra. Here we give the *witness* side: the six
`MapKHas` records, the indexed `MapHas`/`Param`, and — the new content — the **forgetful coercions**
`MapHas src R → MapHas tgt R` whenever `tgt ≤ src`. A user registers a base at a STRONG class
(typically the equivalence `(4,4)`); the solver picks the MINIMAL class each occurrence needs; the
weakening map bridges the two by dropping fields. Proof-light: every forget is just record projection.

The whole diamond `0 < 1 < {2a,2b} < 3 < 4` is generated from six covering edges
  4 ⟶ 3 ⟶ 2a ⟶ 1 ⟶ 0   and   3 ⟶ 2b ⟶ 1
so `weaken` is their composition along the (unique-up-to-confluence) path.
-/
universe u v
namespace Trocq

/- ===================== the class lattice (naming aligned with Lattice.lean) ===================== -/
inductive MapClass | map0 | map1 | map2a | map2b | map3 | map4
deriving DecidableEq, Repr, Inhabited

namespace MapClass
/-- partial order `a ≤ b` on the diamond (same table as Lattice.lean). -/
def le : MapClass → MapClass → Bool
  | map0,  _     => true
  | map1,  map1  => true | map1, map2a => true | map1, map2b => true
  | map1,  map3  => true | map1, map4  => true | map1, _ => false
  | map2a, map2a => true | map2a, map3 => true | map2a, map4 => true | map2a, _ => false
  | map2b, map2b => true | map2b, map3 => true | map2b, map4 => true | map2b, _ => false
  | map3,  map3  => true | map3, map4  => true | map3, _ => false
  | map4,  map4  => true | map4, _ => false
end MapClass

abbrev ParamClass := MapClass × MapClass

/- ===================== the six graded records ===================== -/
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

/-- the structure a relation carries at a given map-class (ULift on the small-universe levels). -/
def MapHas : MapClass → {A B : Type u} → (A → B → Type v) → Type (max u v)
  | .map0,  _, _, R => ULift.{v} (Map0Has R)
  | .map1,  _, _, R => ULift.{v} (Map1Has R)
  | .map2a, _, _, R => Map2aHas R
  | .map2b, _, _, R => ULift.{v} (Map2bHas R)
  | .map3,  _, _, R => Map3Has R
  | .map4,  _, _, R => Map4Has R

structure Param (m n : MapClass) (A B : Type u) where
  R      : A → B → Type v
  cov    : MapHas m R
  contra : MapHas n (fun b a => R a b)

/- ===================== the six covering-edge forgets (bare records) ===================== -/
namespace MapClass
variable {A B : Type u} {R : A → B → Type v}

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
  | .map4, .map2b, _, m => ULift.up (e32b (e43 m))
  | .map4, .map1, _, m => ULift.up (e2a1 (e32a (e43 m)))
  | .map4, .map0, _, m => ULift.up (e10 (e2a1 (e32a (e43 m))))
  -- src = map3  (m : Map3Has R)
  | .map3, .map3, _, m => m
  | .map3, .map2a, _, m => e32a m
  | .map3, .map2b, _, m => ULift.up (e32b m)
  | .map3, .map1, _, m => ULift.up (e2a1 (e32a m))
  | .map3, .map0, _, m => ULift.up (e10 (e2a1 (e32a m)))
  | .map3, .map4, h, _ => nomatch h
  -- src = map2a  (m : Map2aHas R)
  | .map2a, .map2a, _, m => m
  | .map2a, .map1, _, m => ULift.up (e2a1 m)
  | .map2a, .map0, _, m => ULift.up (e10 (e2a1 m))
  | .map2a, .map4, h, _ => nomatch h
  | .map2a, .map3, h, _ => nomatch h
  | .map2a, .map2b, h, _ => nomatch h
  -- src = map2b  (m : ULift (Map2bHas R))
  | .map2b, .map2b, _, m => m
  | .map2b, .map1, _, m => ULift.up (e2b1 m.down)
  | .map2b, .map0, _, m => ULift.up (e10 (e2b1 m.down))
  | .map2b, .map4, h, _ => nomatch h
  | .map2b, .map3, h, _ => nomatch h
  | .map2b, .map2a, h, _ => nomatch h
  -- src = map1  (m : ULift (Map1Has R))
  | .map1, .map1, _, m => m
  | .map1, .map0, _, m => ULift.up (e10 m.down)
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
variable {A B : Type u}

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

/- ===================== demo: weaken the registered Nat ≃ Unary witness ===================== -/
inductive Unary | z | s (n : Unary) deriving Repr
def toNat : Unary → Nat | .z => 0 | .s n => toNat n + 1
def ofNat : Nat → Unary | 0 => .z | n+1 => .s (ofNat n)
theorem toNat_ofNat : ∀ n, toNat (ofNat n) = n
  | 0 => rfl
  | n+1 => by show toNat (ofNat n) + 1 = n + 1; rw [toNat_ofNat n]
theorem ofNat_toNat : ∀ u, ofNat (toNat u) = u
  | .z => rfl
  | .s n => by show Unary.s (ofNat (toNat n)) = Unary.s n; rw [ofNat_toNat n]

def RNU : Nat → Unary → Type := fun n u => PLift (toNat u = n)
def RN : Param.{0,0} .map4 .map4 Nat Unary where
  R := RNU
  cov := { map := ofNat, map_in_R := fun n u h => PLift.up (by subst h; exact toNat_ofNat n),
           R_in_map := fun n u r => by have h := r.down; rw [← h, ofNat_toNat],
           R_in_mapK := fun _ _ _ => rfl }
  contra := { map := toNat, map_in_R := fun u n h => PLift.up h,
              R_in_map := fun u n r => r.down, R_in_mapK := fun _ _ _ => rfl }

section Tests
-- the forgets COMPUTE: the forward map survives every downgrade, by `rfl`.
example : (RN.toRetraction.cov).map = ofNat := rfl
example : (RN.toSection.cov).map = ofNat := rfl
example : (RN.toFunction.cov).down.map = ofNat := rfl          -- map1 cov is ULift-wrapped
example : (RN.toRetraction.contra).map = toNat := rfl          -- map2a contra: the backward map
-- the soundness field also survives where it should (retraction keeps cov's map_in_R):
example : ∀ n u, ofNat n = u → RNU n u := (RN.toRetraction.cov).map_in_R
-- bottom is the bare relation, with no maps at all:
example : (RN.toRel).R = RNU := rfl
end Tests

#print axioms RN
end Trocq
