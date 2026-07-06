/-
The UNIVERSE construction: relating `Type` to `Type`.

The no-univalence ceiling is (2a,2a): `mapInR : A = A' → Param A A'` is `Eq.rec` (free), but completeness
`rInMap : Param A A' → A = A'` would need univalence — so `Type` is blocked above 2a (`mkUniv` enforces
the cap directly). The relation a `Param_Type` carries between `A` and `A'` is itself a `Param p q A A'`,
and that INNER class `(p,q)` is independent of the (capped) outer class: it records how strongly the bound
type variable is related. The inner witness is `paramRefl` (the identity equivalence) weakened to `(p,q)`;
`paramTypeAt m n p q` is the sole combinator — built at the `(2a,2a)` ceiling and weakened to the outer
class `(m,n) ≤ (2a,2a)`.
-/
import LeTrocq.Core.Param
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
      mapInR := fun _ _ h => PLift.up h
      rInMap := fun _ _ r => r.down
      rInMapK := fun _ _ _ => rfl }
  contra :=
    { map := id
      mapInR := fun _ _ h => PLift.up h.symm
      rInMap := fun _ _ r => r.down.symm
      rInMapK := fun _ _ r => by cases r with | up h => cases h; rfl }

/-- reflexive `Param` at ANY class, by weakening `paramRefl` from the top. -/
def paramIdAt (p q : MapClass) (A : Sort u) : Param.{u,0} p q A A :=
  (paramRefl A).weaken (MapClass.le_map4 p) (MapClass.le_map4 q)

/-- THE UNIVERSE COMBINATOR, at outer class `(m,n) ≤ (2a,2a)` and carrying INNER relation class `(p,q)` (the
    `Map_Type` table): the relation is `fun A A' => Param p q A A'`, and `mapInR : A = A' → Param p q A A'`
    is `Eq.rec` of `paramIdAt` — no univalence. It is built at the `(2a,2a)` ceiling and weakened to `(m,n)`;
    the inner class `(p,q)` is free (it records how strongly the bound type variable is related). This is the
    driver's entry point — `mkUniv` calls it with inner `(4,4)`, the pinned top for a bound type variable. -/
def paramTypeAt (m n p q : MapClass)
    (hm : MapClass.le m map2a = true) (hn : MapClass.le n map2a = true) :
    Param m n (Type w) (Type w) :=
  Param.weaken hm hn <| show Param map2a map2a (Type w) (Type w) from
    { R := fun A A' => Param p q A A'
      cov :=
        { map := id
          mapInR := fun A A' h => by subst h; exact paramIdAt p q A }
      contra :=
        { map := id
          mapInR := fun A' A h => by subst h; exact paramIdAt p q A' } }

/-- the PROP universe combinator at the TOP class `(4,4)`. Unlike the `Type` universe (capped at `2a`
    by the absence of univalence), `Prop` reaches the full equivalence: `mapInR` is `Eq.rec`,
    completeness `rInMap` is **`propext`** (which Lean has), and the coherence `rInMapK` is free by
    **proof irrelevance** (the relation `PLift (P ↔ P')` is a subsingleton). Note the relation is `Iff`,
    not a sub-`Param` — a *specific* prop can't be a `Param` argument over the `Type`-based hierarchy. -/
def paramProp : Param map4 map4 Prop Prop where
  R := fun P P' => PLift (P ↔ P')
  cov :=
    { map := id
      mapInR := fun _ _ h => by subst h; exact PLift.up Iff.rfl
      rInMap := fun _ _ r => propext r.down
      rInMapK := fun _ _ r => by cases r; rfl }
  contra :=
    { map := id
      mapInR := fun _ _ h => by subst h; exact PLift.up Iff.rfl
      rInMap := fun _ _ r => (propext r.down).symm
      rInMapK := fun _ _ r => by cases r; rfl }

/-- the Prop universe combinator at any class (weaken the `(4,4)` ceiling). -/
def paramPropAt (m n : MapClass) : Param m n Prop Prop :=
  paramProp.weaken (MapClass.le_map4 m) (MapClass.le_map4 n)

/-- read the equivalence `P ↔ P'` off a `Param map1 map1` between two propositions (its forward/backward
    maps). Used by `Transfer.assembleTerm` to project a proposition's `(1,1)` witness to `PLift (P ↔ P')`. -/
def iffOfParam {P P' : Prop} (p : Param map1 map1 P P') : P ↔ P' := ⟨p.cov.map, p.contra.map⟩

/-- `MapHas m` for the trivial Prop relation `fun _ _ => PLift True`, from a SINGLE forward map `P → P'`.
    Because `P'` is a proposition, every completeness field is FREE: `mapInR` returns `PLift.up trivial`,
    and `rInMap`/`rInMapK` are `rfl` (two proofs of the `Prop` `P'` are defeq, and `PLift True` is a
    subsingleton). So a proposition's transport carries no data above class 1 — this is the whole reason a
    `Prop` part is only ever demanded up to `meet · map1`. -/
def propMapHas {P P' : Prop} (map : P → P') :
    (m : MapClass) → MapHas m (fun (_ : P) (_ : P') => PLift True)
  | map0  => {}
  | map1  => { map := map }
  | map2a => { map := map, mapInR := fun _ _ _ => PLift.up trivial }
  | map2b => { map := map, rInMap := fun _ _ _ => rfl }
  | map3  => { map := map, mapInR := fun _ _ _ => PLift.up trivial, rInMap := fun _ _ _ => rfl }
  | map4  => { map := map, mapInR := fun _ _ _ => PLift.up trivial, rInMap := fun _ _ _ => rfl,
               rInMapK := fun _ _ _ => rfl }

/-- a `Param m n` between PROPOSITIONS built DIRECTLY at `(m,n)` from the two implications (no weaken-from-top).
    Each direction consumes only the corresponding implication, and only when its class is ≥ 1 (`propMapHas`
    discards it at `map0`). The shared builder for `Prop` relators with no gradeable `Prop` PART (`Eq`, a
    predicate); the connectives grade their parts and use `propMapHas` per class-arm directly. -/
def paramPropFromMaps (m n : MapClass) {P P' : Prop} (fwd : P → P') (bwd : P' → P) : Param m n P P' where
  R      := fun _ _ => PLift True
  cov    := propMapHas fwd m
  contra := propMapHas bwd n

end LeTrocq
