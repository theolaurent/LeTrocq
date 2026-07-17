
import LeTrocq.Core.Class
universe u v
namespace LeTrocq

-- the six graded records (over `Sort u`, so `Prop` fits too)
structure Map0 {A B : Sort u} (_R : A → B → Type v) : Sort (max u (v+1)) where
structure Map1 {A B : Sort u} (_R : A → B → Type v) : Sort (max u (v+1)) where
  map : A → B
structure Map2a {A B : Sort u} (R : A → B → Type v) : Sort (max u (v+1)) where
  map : A → B
  mapInR : ∀ a b, map a = b → R a b
structure Map2b {A B : Sort u} (R : A → B → Type v) : Sort (max u (v+1)) where
  map : A → B
  rInMap : ∀ a b, R a b → map a = b
structure Map3 {A B : Sort u} (R : A → B → Type v) : Sort (max u (v+1)) where
  map : A → B
  mapInR : ∀ a b, map a = b → R a b
  rInMap : ∀ a b, R a b → map a = b
structure Map4 {A B : Sort u} (R : A → B → Type v) : Sort (max u (v+1)) where
  map : A → B
  mapInR : ∀ a b, map a = b → R a b
  rInMap : ∀ a b, R a b → map a = b
  rInMapK : ∀ a b r, mapInR a b (rInMap a b r) = r

/-- the structure a relation carries at a given map-class — all at the uniform `Sort (max u (v+1))`. -/
def Map : MapClass → {A B : Sort u} → (A → B → Type v) → Sort (max u (v+1))
  | .map0,  _, _, R => Map0 R
  | .map1,  _, _, R => Map1 R
  | .map2a, _, _, R => Map2a R
  | .map2b, _, _, R => Map2b R
  | .map3,  _, _, R => Map3 R
  | .map4,  _, _, R => Map4 R

structure Param (m n : MapClass) (A B : Sort u) where
  R      : A → B → Type v
  cov    : Map m R
  contra : Map n (fun b a => R a b)

/-- A class-4 relation is necessarily a subsingleton: `rInMap` sends related elements to proofs of
    `map a = b`, equal by proof irrelevance, so `rInMapK` forces them equal. Makes the `(4,4)` coherence
    free on any relation reachable from class-4 data. -/
theorem Map4.subsingleton {A B : Sort u} {R : A → B → Type v} (m : Map4 R) (a : A) (b : B) :
    Subsingleton (R a b) :=
  ⟨fun r₁ r₂ => by rw [← m.rInMapK a b r₁, ← m.rInMapK a b r₂]⟩

/-- symmetry: a `Param m n A B` is a `Param n m B A` on the reversed relation (swap cov/contra). -/
def Param.sym {A B : Sort u} {m n : MapClass} (p : Param.{u,v} m n A B) : Param.{u,v} n m B A where
  R := fun b a => p.R a b
  cov := p.contra
  contra := p.cov

/- ===================== the six covering-edge forgets (bare records) ===================== -/
namespace MapClass
variable {A B : Sort u} {R : A → B → Type v}

def forget43  (h : Map4 R)  : Map3 R  := { map := h.map, mapInR := h.mapInR, rInMap := h.rInMap }
def forget32a (h : Map3 R)  : Map2a R := { map := h.map, mapInR := h.mapInR }
def forget32b (h : Map3 R)  : Map2b R := { map := h.map, rInMap := h.rInMap }
def forget2a1 (h : Map2a R) : Map1 R  := { map := h.map }
def forget2b1 (h : Map2b R) : Map1 R  := { map := h.map }
def forget10  (_ : Map1 R)  : Map0 R  := {}

def weaken : (src tgt : MapClass) → MapClass.le tgt src → Map src R → Map tgt R
  -- src = map4  (m : Map4Has R)
  | .map4, .map4, _, m => m
  | .map4, .map3, _, m => forget43 m
  | .map4, .map2a, _, m => forget32a (forget43 m)
  | .map4, .map2b, _, m => forget32b (forget43 m)
  | .map4, .map1, _, m => forget2a1 (forget32a (forget43 m))
  | .map4, .map0, _, m => forget10 (forget2a1 (forget32a (forget43 m)))
  -- src = map3  (m : Map3Has R)
  | .map3, .map3, _, m => m
  | .map3, .map2a, _, m => forget32a m
  | .map3, .map2b, _, m => forget32b m
  | .map3, .map1, _, m => forget2a1 (forget32a m)
  | .map3, .map0, _, m => forget10 (forget2a1 (forget32a m))
  | .map3, .map4, h, _ => nomatch h
  -- src = map2a  (m : Map2aHas R)
  | .map2a, .map2a, _, m => m
  | .map2a, .map1, _, m => forget2a1 m
  | .map2a, .map0, _, m => forget10 (forget2a1 m)
  | .map2a, .map4, h, _ => nomatch h
  | .map2a, .map3, h, _ => nomatch h
  | .map2a, .map2b, h, _ => nomatch h
  -- src = map2b  (m : Map2bHas R)
  | .map2b, .map2b, _, m => m
  | .map2b, .map1, _, m => forget2b1 m
  | .map2b, .map0, _, m => forget10 (forget2b1 m)
  | .map2b, .map4, h, _ => nomatch h
  | .map2b, .map3, h, _ => nomatch h
  | .map2b, .map2a, h, _ => nomatch h
  -- src = map1  (m : Map1Has R)
  | .map1, .map1, _, m => m
  | .map1, .map0, _, m => forget10 m
  | .map1, .map4, h, _ => nomatch h
  | .map1, .map3, h, _ => nomatch h
  | .map1, .map2a, h, _ => nomatch h
  | .map1, .map2b, h, _ => nomatch h
  -- src = map0  (m : Map0Has R)
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

end LeTrocq
