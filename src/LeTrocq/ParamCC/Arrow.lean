/-
The ARROW construction: building `Param … (A→B) (A'→B')` from witnesses for the parts.

  • `RArrow`              — the respectful relation (= Mathlib `Relator.LiftFun`).
  • `mapArrowVariance`/`arrowVariance` — the GRADING table: output class → the minimal part classes to build it.
  • `arrowCov`/`arrowContra` + `paramArrow` — the GRADED family: arrow at every output class incl. (4,4)
    (the (4,4) coherence free by `Map4Has.subsingleton`), with parts at the `arrowVariance`-minimal classes.

(The arrow stays over `Type u`; relating `Prop` *bodies* goes through `Forall`/the universe combinators,
whose `Param` arguments are `Sort`-general.)
-/
import LeTrocq.Hierarchy
universe u v
namespace LeTrocq
open MapClass

/- ===================== the arrow relation (= Mathlib `Relator.LiftFun`) ===================== -/
/-- the respectful relation: related inputs ↦ related outputs. -/
def RArrow {A B A' B' : Type u} (RA : A → A' → Type v) (RB : B → B' → Type v) :
    (A → B) → (A' → B') → Type (max u v) :=
  fun f f' => ∀ a a', RA a a' → RB (f a) (f' a')

/- ===================== the arrow GRADING table (output class → minimal part classes) ===================== -/
/-- per-map-class minimal (domain, codomain) classes for a non-dependent arrow (verbatim from Trocq's
    `class.elpi`); the domain is `(cov, contra)`, likewise the codomain. -/
def mapArrowVariance : MapClass → (ParamClass × ParamClass)
  | map0  => ((map0,map0), (map0,map0))
  | map1  => ((map0,map1), (map1,map0))
  | map2a => ((map0,map2b),(map2a,map0))
  | map2b => ((map0,map2a),(map2b,map0))
  | map3  => ((map0,map3), (map3,map0))
  | map4  => ((map0,map4), (map4,map0))

/-- minimal (domain-class, codomain-class) needed to build the arrow at output class `c`: the cov requirement
    joined with the negated contra one (the two transport directions combined). `Transfer.assemble` inverts a
    demand through this to grade the parts; `paramArrow`'s type consumes it. -/
def arrowVariance (c : ParamClass) : ParamClass × ParamClass :=
  let (am, bm) := mapArrowVariance c.1
  let (an, bn) := mapArrowVariance c.2
  (ParamClass.join am (ParamClass.negate an), ParamClass.join bm (ParamClass.negate bn))

/- ===================== the graded arrow family (every output class, incl. (4,4)) ===================== -/
/-- the covariant half `MapHas m (RArrow RA RB)` from A's contra + B's cov (one arm per class). At
    `map4` the coherence `R_in_mapK` is FREE: class-4 parts have subsingleton relations
    (`Map4Has.subsingleton`), so the arrow relation is a subsingleton and any two proofs are equal. -/
def arrowCov {A B A' B' : Type u} :
    (m : MapClass) →
    (pa : Param (mapArrowVariance m).1.1 (mapArrowVariance m).1.2 A A') →
    (pb : Param (mapArrowVariance m).2.1 (mapArrowVariance m).2.2 B B') →
    MapHas m (RArrow pa.R pb.R)
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := fun f a' => pb.cov.map (f (pa.contra.map a')) }
  | map2a, pa, pb =>
      { map := fun f a' => pb.cov.map (f (pa.contra.map a'))
        map_in_R := fun f f' h a a' raa => by
          have ha : pa.contra.map a' = a := pa.contra.R_in_map a' a raa
          have hf : f' a' = pb.cov.map (f (pa.contra.map a')) := (congrFun h a').symm
          rw [hf, ha]; exact pb.cov.map_in_R (f a) (pb.cov.map (f a)) rfl }
  | map2b, pa, pb =>
      { map := fun f a' => pb.cov.map (f (pa.contra.map a'))
        R_in_map := fun f f' r => funext fun a' => by
          have hra : pa.R (pa.contra.map a') a' := pa.contra.map_in_R a' (pa.contra.map a') rfl
          exact pb.cov.R_in_map _ _ (r (pa.contra.map a') a' hra) }
  | map3,  pa, pb =>
      { map := fun f a' => pb.cov.map (f (pa.contra.map a'))
        map_in_R := fun f f' h a a' raa => by
          have ha : pa.contra.map a' = a := pa.contra.R_in_map a' a raa
          have hf : f' a' = pb.cov.map (f (pa.contra.map a')) := (congrFun h a').symm
          rw [hf, ha]; exact pb.cov.map_in_R (f a) (pb.cov.map (f a)) rfl
        R_in_map := fun f f' r => funext fun a' => by
          have hra : pa.R (pa.contra.map a') a' := pa.contra.map_in_R a' (pa.contra.map a') rfl
          exact pb.cov.R_in_map _ _ (r (pa.contra.map a') a' hra) }
  | map4,  pa, pb =>
      { map := fun f a' => pb.cov.map (f (pa.contra.map a'))
        map_in_R := fun f f' h a a' raa => by
          have ha : pa.contra.map a' = a := pa.contra.R_in_map a' a raa
          have hf : f' a' = pb.cov.map (f (pa.contra.map a')) := (congrFun h a').symm
          rw [hf, ha]; exact pb.cov.map_in_R (f a) (pb.cov.map (f a)) rfl
        R_in_map := fun f f' r => funext fun a' => by
          have hra : pa.R (pa.contra.map a') a' := pa.contra.map_in_R a' (pa.contra.map a') rfl
          exact pb.cov.R_in_map _ _ (r (pa.contra.map a') a' hra)
        R_in_mapK := fun f f' _ => by
          haveI : Subsingleton (RArrow pa.R pb.R f f') :=
            ⟨fun x y => funext fun a => funext fun a' => funext fun raa =>
              @Subsingleton.elim _ (pb.cov.subsingleton (f a) (f' a')) _ _⟩
          exact Subsingleton.elim _ _ }

/-- the contravariant half `MapHas n (sym (RArrow RA RB))` from A's cov + B's contra (the mirror). -/
def arrowContra {A B A' B' : Type u} :
    (n : MapClass) →
    (pa : Param (mapArrowVariance n).1.2 (mapArrowVariance n).1.1 A A') →
    (pb : Param (mapArrowVariance n).2.2 (mapArrowVariance n).2.1 B B') →
    MapHas n (fun (f' : A' → B') (f : A → B) => RArrow pa.R pb.R f f')
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := fun f' a => pb.contra.map (f' (pa.cov.map a)) }
  | map2a, pa, pb =>
      { map := fun f' a => pb.contra.map (f' (pa.cov.map a))
        map_in_R := fun f' f h a a' raa => by
          have ha : pa.cov.map a = a' := pa.cov.R_in_map a a' raa
          have hf : f a = pb.contra.map (f' (pa.cov.map a)) := (congrFun h a).symm
          rw [hf, ha]; exact pb.contra.map_in_R (f' a') (pb.contra.map (f' a')) rfl }
  | map2b, pa, pb =>
      { map := fun f' a => pb.contra.map (f' (pa.cov.map a))
        R_in_map := fun f' f r => funext fun a => by
          have hra : pa.R a (pa.cov.map a) := pa.cov.map_in_R a (pa.cov.map a) rfl
          exact pb.contra.R_in_map _ _ (r a (pa.cov.map a) hra) }
  | map3,  pa, pb =>
      { map := fun f' a => pb.contra.map (f' (pa.cov.map a))
        map_in_R := fun f' f h a a' raa => by
          have ha : pa.cov.map a = a' := pa.cov.R_in_map a a' raa
          have hf : f a = pb.contra.map (f' (pa.cov.map a)) := (congrFun h a).symm
          rw [hf, ha]; exact pb.contra.map_in_R (f' a') (pb.contra.map (f' a')) rfl
        R_in_map := fun f' f r => funext fun a => by
          have hra : pa.R a (pa.cov.map a) := pa.cov.map_in_R a (pa.cov.map a) rfl
          exact pb.contra.R_in_map _ _ (r a (pa.cov.map a) hra) }
  | map4,  pa, pb =>
      { map := fun f' a => pb.contra.map (f' (pa.cov.map a))
        map_in_R := fun f' f h a a' raa => by
          have ha : pa.cov.map a = a' := pa.cov.R_in_map a a' raa
          have hf : f a = pb.contra.map (f' (pa.cov.map a)) := (congrFun h a).symm
          rw [hf, ha]; exact pb.contra.map_in_R (f' a') (pb.contra.map (f' a')) rfl
        R_in_map := fun f' f r => funext fun a => by
          have hra : pa.R a (pa.cov.map a) := pa.cov.map_in_R a (pa.cov.map a) rfl
          exact pb.contra.R_in_map _ _ (r a (pa.cov.map a) hra)
        R_in_mapK := fun f' f _ => by
          haveI : Subsingleton (RArrow pa.R pb.R f f') :=
            ⟨fun x y => funext fun a => funext fun a' => funext fun raa =>
              @Subsingleton.elim _ (pb.contra.subsingleton (f' a') (f a)) _ _⟩
          exact Subsingleton.elim _ _ }

/-- arrow at ANY output class `(m,n)`, incl. `(4,4)`, from parts at the `arrowVariance`-minimal classes.
    The single joined-class part is weakened down to what each half (cov/contra) consumes; every
    weakening obligation is `join ≥ component`, discharged by `cases m <;> cases n <;> rfl`. -/
def paramArrow {A B A' B' : Type u} (m n : MapClass)
    (pa : Param (arrowVariance (m, n)).1.1 (arrowVariance (m, n)).1.2 A A')
    (pb : Param (arrowVariance (m, n)).2.1 (arrowVariance (m, n)).2.2 B B') :
    Param m n (A → B) (A' → B') where
  R := RArrow pa.R pb.R
  cov := arrowCov m
    ((pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param (mapArrowVariance m).1.1 (mapArrowVariance m).1.2 A A')
    ((pb.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param (mapArrowVariance m).2.1 (mapArrowVariance m).2.2 B B')
  contra := arrowContra n
    ((pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param (mapArrowVariance n).1.2 (mapArrowVariance n).1.1 A A')
    ((pb.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param (mapArrowVariance n).2.2 (mapArrowVariance n).2.1 B B')

end LeTrocq
