/-
The UNIVERSE construction: relating `Type` to `Type`.

The no-univalence ceiling is (2a,2a): `map_in_R : A = A' → Param A A'` is `Eq.rec` (free), but completeness
`R_in_map : Param A A' → A = A'` would need univalence — so `Type` is blocked above 2a (`mkUniv` enforces
the cap directly). The relation a `Param_Type` carries between `A` and `A'` is itself a `Param p q A A'`,
and that INNER class `(p,q)` is independent of the (capped) outer class: it records how strongly the bound
type variable is related. The inner witness is `paramRefl` (the identity equivalence) weakened to `(p,q)`;
`paramTypeAtInner` is the general form, `paramType` the `(1,1)`-inner specialization.
-/
import LeTrocq.Hierarchy
universe u w
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

/-- the universe combinator at the ceiling (2a,2a), carrying INNER relation class `(p,q)` (the
    `Map_Type` table). `map_in_R : A = A' → Param p q A A'` is `Eq.rec` of `paramIdAt` — no univalence;
    the inner class `(p,q)` is free (it records how the bound type variable must be related). -/
def paramTypeInner (p q : MapClass) : Param map2a map2a (Type w) (Type w) where
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
    Param m n (Type w) (Type w) :=
  (paramTypeInner p q).weaken hm hn

/-- the universe combinator at (2a,2a) with the simplest inner class (1,1). -/
def paramType : Param map2a map2a (Type w) (Type w) := paramTypeInner map1 map1

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

/-- read the equivalence `P ↔ P'` off a `Param map1 map1` between two propositions (its forward/backward
    maps). Used by `Transfer.assembleTerm` to project a proposition's `(1,1)` witness to `PLift (P ↔ P')`. -/
def iffOfParam {P P' : Prop} (p : Param map1 map1 P P') : P ↔ P' := ⟨p.cov.map, p.contra.map⟩

/-- `MapHas m` for the trivial Prop relation `fun _ _ => PLift True`, from a SINGLE forward map `P → P'`.
    Because `P'` is a proposition, every completeness field is FREE: `map_in_R` returns `PLift.up trivial`,
    and `R_in_map`/`R_in_mapK` are `rfl` (two proofs of the `Prop` `P'` are defeq, and `PLift True` is a
    subsingleton). So a proposition's transport carries no data above class 1 — this is the whole reason a
    `Prop` part is only ever demanded up to `meet · map1`. -/
def propMapHas {P P' : Prop} (map : P → P') :
    (m : MapClass) → MapHas m (fun (_ : P) (_ : P') => PLift True)
  | map0  => {}
  | map1  => { map := map }
  | map2a => { map := map, map_in_R := fun _ _ _ => PLift.up trivial }
  | map2b => { map := map, R_in_map := fun _ _ _ => rfl }
  | map3  => { map := map, map_in_R := fun _ _ _ => PLift.up trivial, R_in_map := fun _ _ _ => rfl }
  | map4  => { map := map, map_in_R := fun _ _ _ => PLift.up trivial, R_in_map := fun _ _ _ => rfl,
               R_in_mapK := fun _ _ _ => rfl }

/-- a `Param m n` between PROPOSITIONS built DIRECTLY at `(m,n)` from the two implications (no weaken-from-top).
    Each direction consumes only the corresponding implication, and only when its class is ≥ 1 (`propMapHas`
    discards it at `map0`). The shared builder for `Prop` relators with no gradeable `Prop` PART (`Eq`, a
    predicate); the connectives grade their parts and use `propMapHas` per class-arm directly. -/
def paramPropMapsAt (m n : MapClass) {P P' : Prop} (fwd : P → P') (bwd : P' → P) : Param m n P P' where
  R      := fun _ _ => PLift True
  cov    := propMapHas fwd m
  contra := propMapHas bwd n

end LeTrocq
