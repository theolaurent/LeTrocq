/-
The UNIVERSE construction: relating `Type` to `Type`.

The no-univalence ceiling is class (2a,2a): `map_in_R : A = A' → Param A A'` is `Eq.rec` (free), but the
completeness field `R_in_map : Param A A' → A = A'` would need univalence — so `Type` is BLOCKED above 2a,
exactly what `Lattice`'s `requiresAxiom`/`depType` encode.

The relation a `Param_Type` *carries* between `A` and `A'` is itself a `Param p q A A'` — and that INNER
class `(p,q)` is **independent** of the (capped) outer class: it just records how strongly the bound type
variable is related, which is whatever the body demands. This is LeTrocq's `Map_Type` table. The inner
witness is built by weakening the reflexive identity `paramRefl` (the identity IS an equivalence, so it
exists at the top class) down to `(p,q)`. `paramTypeAtInner` is the general form; `paramType`/`paramTypeAt`
are the `(1,1)`-inner specializations kept for the simple cases.
-/
import LeTrocq.Hierarchy
universe u
namespace LeTrocq
open MapClass

/-- every class is ≤ the top class. -/
theorem MapClass.le_map4 (c : MapClass) : MapClass.le c map4 = true := by cases c <;> rfl

/-- the reflexive identity `Param` at the TOP class (4,4): `R a b := PLift (a = b)`. The identity map is
    trivially an equivalence, so all four fields hold (the coherence by structure-eta / `Eq` casing). -/
def paramRefl (A : Sort u) : Param.{u,0} map4 map4 A A where
  R := fun a b => PLift (a = b)
  cov :=
    { map := id
      map_in_R := fun _ _ h => PLift.up h
      R_in_map := fun _ _ r => r.down
      R_in_mapK := fun _ _ _ => rfl }
  contra :=
    { map := id
      map_in_R := fun _ _ h => PLift.up h.symm
      R_in_map := fun _ _ r => r.down.symm
      R_in_mapK := fun _ _ r => by cases r with | up h => cases h; rfl }

/-- reflexive `Param` at ANY class, by weakening `paramRefl` from the top. -/
def paramIdAt (p q : MapClass) (A : Sort u) : Param.{u,0} p q A A :=
  (paramRefl A).weaken (MapClass.le_map4 p) (MapClass.le_map4 q)

/-- a reflexive `Param` at (1,1) — the identity. -/
def paramId (A : Sort u) : Param.{u,0} map1 map1 A A := paramIdAt map1 map1 A

/-- the universe combinator at the ceiling (2a,2a), carrying INNER relation class `(p,q)` (the
    `Map_Type` table). `map_in_R : A = A' → Param p q A A'` is `Eq.rec` of `paramIdAt` — no univalence;
    the inner class `(p,q)` is free (it records how the bound type variable must be related). -/
def paramTypeInner (p q : MapClass) : Param map2a map2a (Type 0) (Type 0) where
  R := fun A A' => Param p q A A'
  cov :=
    { map := id
      map_in_R := fun A A' h => by subst h; exact paramIdAt p q A }
  contra :=
    { map := id
      map_in_R := fun A' A h => by subst h; exact paramIdAt p q A' }

/-- the universe combinator at outer class `≤ (2a,2a)` with inner relation class `(p,q)`. -/
def paramTypeAtInner (m n p q : MapClass)
    (hm : MapClass.le m map2a = true) (hn : MapClass.le n map2a = true) :
    Param m n (Type 0) (Type 0) :=
  (paramTypeInner p q).weaken hm hn

/-- the universe combinator at (2a,2a) with the simplest inner class (1,1). -/
def paramType : Param map2a map2a (Type 0) (Type 0) := paramTypeInner map1 map1

/-- the universe combinator at any class `≤ (2a,2a)`, inner class (1,1). -/
def paramTypeAt (m n : MapClass)
    (hm : MapClass.le m map2a = true) (hn : MapClass.le n map2a = true) :
    Param m n (Type 0) (Type 0) :=
  paramTypeAtInner m n map1 map1 hm hn

/-- the PROP universe combinator at the TOP class `(4,4)`. Unlike the `Type` universe (capped at `2a`
    by the absence of univalence), `Prop` reaches the full equivalence: `map_in_R` is `Eq.rec`,
    completeness `R_in_map` is **`propext`** (which Lean has), and the coherence `R_in_mapK` is free by
    **proof irrelevance** (the relation `PLift (P ↔ P')` is a subsingleton). Note the relation is `Iff`,
    not a sub-`Param` — a *specific* prop can't be a `Param` argument over the `Type`-based hierarchy. -/
def paramProp : Param map4 map4 Prop Prop where
  R := fun P P' => PLift (P ↔ P')
  cov :=
    { map := id
      map_in_R := fun _ _ h => by subst h; exact PLift.up Iff.rfl
      R_in_map := fun _ _ r => propext r.down
      R_in_mapK := fun _ _ r => by cases r; rfl }
  contra :=
    { map := id
      map_in_R := fun _ _ h => by subst h; exact PLift.up Iff.rfl
      R_in_map := fun _ _ r => (propext r.down).symm
      R_in_mapK := fun _ _ r => by cases r; rfl }

/-- the Prop universe combinator at any class (weaken the `(4,4)` ceiling). -/
def paramPropAt (m n : MapClass) : Param m n Prop Prop :=
  paramProp.weaken (MapClass.le_map4 m) (MapClass.le_map4 n)

end LeTrocq
