/-

Universe: relating `Type` to `Type` and `Prop` to `Prop`.

-- TODO: move tha comment?
In the absence of univalence, the ceiling of `Type` is (2a, 2a).
`mapInR : A = A' → Param A A'` is free, while
`rInMap : Param A A' → A = A'` would need univalence.

`Prop` instead reaches (4,4), via `propext` (see below).

The relation a `Param_Type` carries is itself a `Param p q A A'`;
that inner class `(p,q)` is free (it records how strongly the bound
type variable is related).
`paramTypeAt m n p q` is the sole combinator — built at the `(2a,2a)` ceiling and
weakened to the outer class `(m,n) ≤ (2a,2a)`.

-/
import LeTrocq.Core.Param
universe u w
namespace LeTrocq
open MapClass

-- TODO: why is that here and not in Core/ ?
theorem MapClass.le_map4 (c : MapClass) : MapClass.le c map4 := by cases c <;> rfl

-- TODO: a note about why it is reasonable in presence of type variables
/- the reflexive identity `Param` at the top class (4,4): `R a b := PLift (a = b)`, the identity map being
   trivially an equivalence. -/
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

/-- the universe combinator, at outer class `(m,n) ≤ (2a,2a)` carrying inner relation class `(p,q)`: relation
    `fun A A' => Param p q A A'`, `mapInR` is `Eq.rec` of `paramIdAt` (no univalence). Built at the `(2a,2a)`
    ceiling and weakened to `(m,n)`. The driver's entry point; `mkUniv` calls it with inner `(4,4)`. -/
def paramTypeAt (m n p q : MapClass)
    (hm : MapClass.le m map2a) (hn : MapClass.le n map2a) :
    Param m n (Type w) (Type w) :=
  Param.weaken hm hn <| show Param map2a map2a (Type w) (Type w) from
    { R := fun A A' => Param p q A A'
      cov :=
        { map := id
          mapInR := fun A A' h => by subst h; exact paramIdAt p q A }
      contra :=
        { map := id
          mapInR := fun A' A h => by subst h; exact paramIdAt p q A' } }

/-- the Prop universe combinator at the top class `(4,4)`. Unlike `Type` (capped at 2a), `Prop` reaches the
    full equivalence: `rInMap` is `propext` (which Lean has) and the coherence is free by proof irrelevance.
    The relation is `Iff`, not a sub-`Param` — a specific prop can't be a `Param` argument over the
    `Type`-based hierarchy. -/
def paramProp := paramRefl Prop

-- TODO: just inline weaken
/- the Prop universe combinator at any class (weaken the `(4,4)` ceiling). -/
def paramPropAt (m n : MapClass) : Param m n Prop Prop :=
  paramProp.weaken (MapClass.le_map4 m) (MapClass.le_map4 n)

-- TODO: could these become some kind of coercion?
def iffOfParam {P P' : Prop} (p : Param map1 map1 P P') : P ↔ P' := ⟨p.cov.map, p.contra.map⟩
def paramOfIff {P P' : Prop} (p : P ↔ P') : Param map4 map4 P P' :=
    { R := fun _ _ => PLift True
      cov :=
        { map := p.1
          mapInR := fun _ _ _ => PLift.up trivial
          rInMap := fun _ _ _ => rfl
          rInMapK := fun _ _ _ => rfl }
      contra :=
        { map := p.2
          mapInR := fun _ _ _ => PLift.up trivial
          rInMap := fun _ _ _ => rfl
          rInMapK := fun _ _ _ => rfl }
    }

-- TODO: remove that
/-- `Map m` for the trivial Prop relation `fun _ _ => PLift True`, from a single forward map `P → P'`.
    Since `P'` is a proposition, every completeness field is free — so a proposition's transport carries no
    data above class 1, which is why a `Prop` part is only ever demanded up to `meet · map1`. -/
def propMap {P P' : Prop} (map : P → P') :
    (m : MapClass) → Map m (fun (_ : P) (_ : P') => PLift True)
  | map0  => {}
  | map1  => { map := map }
  | map2a => { map := map, mapInR := fun _ _ _ => PLift.up trivial }
  | map2b => { map := map, rInMap := fun _ _ _ => rfl }
  | map3  => { map := map, mapInR := fun _ _ _ => PLift.up trivial, rInMap := fun _ _ _ => rfl }
  | map4  => { map := map, mapInR := fun _ _ _ => PLift.up trivial, rInMap := fun _ _ _ => rfl,
               rInMapK := fun _ _ _ => rfl }


-- TODO: this is just paramOfiff
/-- a `Param m n` between propositions built directly at `(m,n)` from the two implications (no weaken-from-top),
    each consumed only when its class is ≥ 1. Shared builder for `Prop` relators with no gradeable `Prop` part
    (`Eq`, a predicate); connectives grade their parts and use `propMap` per class-arm directly. -/
def paramPropFromMaps (m n : MapClass) {P P' : Prop} (fwd : P → P') (bwd : P' → P) : Param m n P P' where
  R      := fun _ _ => PLift True
  cov    := propMap fwd m
  contra := propMap bwd n

end LeTrocq
