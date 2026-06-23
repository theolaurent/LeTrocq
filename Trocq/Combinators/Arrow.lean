/-
The ARROW construction: building `Param … (A→B) (A'→B')` from witnesses for the parts.

  • `RArrow`              — the respectful relation (= Mathlib `Relator.LiftFun`).
  • `paramArrowLow`       — the minimal class (0,1): backward map only, ZERO proofs (axiom-free).
  • `paramArrow33`        — class (3,3): full soundness+completeness via funext.
  • `arrowCov`/`arrowContra` + `paramArrow` — the GRADED family: arrow at every output class ≤ (3,3),
    with parts required only at the `depArrow`-minimal classes. `map4` deferred (the (3→4) adjoint
    coherence `R_in_mapK`), discharged by the `le · map3` cap.
-/
import Trocq.Hierarchy
universe u v
namespace Trocq
open MapClass

/- ===================== the arrow relation (= Mathlib `Relator.LiftFun`) ===================== -/
/-- the respectful relation: related inputs ↦ related outputs. -/
def RArrow {A B A' B' : Type u} (RA : A → A' → Type v) (RB : B → B' → Type v) :
    (A → B) → (A' → B') → Type (max u v) :=
  fun f f' => ∀ a a', RA a a' → RB (f a) (f' a')

/- ===================== sample combinators (fixed classes) ===================== -/
section Samples
variable {A B A' B' : Type u} {RA : A → A' → Type v} {RB : B → B' → Type v}

/-- arrow at (0,1): the codomain is only used contravariantly, the domain only covariantly, so all we
    can (and need to) produce is the backward map `(A'→B') → (A→B)`. No `map_in_R`/`R_in_map`/funext. -/
def paramArrowLow (pa : Param.{u,v} map1 map0 A A') (pb : Param.{u,v} map0 map1 B B') :
    Param.{u, max u v} map0 map1 (A → B) (A' → B') where
  R := RArrow pa.R pb.R
  cov := ULift.up {}
  contra := ULift.up { map := fun f' a => pb.contra.down.map (f' (pa.cov.down.map a)) }

/-- arrow at (3,3): from full (3,3) data on domain and codomain. The forward map is
    `B.fwd ∘ f ∘ A.bwd`; completeness in each direction is a `funext` of the parts' completeness. -/
def paramArrow33 (pa : Param.{u,v} map3 map3 A A') (pb : Param.{u,v} map3 map3 B B') :
    Param.{u, max u v} map3 map3 (A → B) (A' → B') where
  R := RArrow pa.R pb.R
  cov :=
    { map := fun f a' => pb.cov.map (f (pa.contra.map a'))
      map_in_R := fun f f' h a a' raa => by
        have ha : pa.contra.map a' = a := pa.contra.R_in_map a' a raa
        have hf : f' a' = pb.cov.map (f (pa.contra.map a')) := (congrFun h a').symm
        rw [hf, ha]; exact pb.cov.map_in_R (f a) (pb.cov.map (f a)) rfl
      R_in_map := fun f f' r => funext fun a' => by
        have hra : pa.R (pa.contra.map a') a' := pa.contra.map_in_R a' (pa.contra.map a') rfl
        exact pb.cov.R_in_map _ _ (r (pa.contra.map a') a' hra) }
  contra :=
    { map := fun f' a => pb.contra.map (f' (pa.cov.map a))
      map_in_R := fun f' f h a a' raa => by
        have ha : pa.cov.map a = a' := pa.cov.R_in_map a a' raa
        have hf : f a = pb.contra.map (f' (pa.cov.map a)) := (congrFun h a).symm
        rw [hf, ha]; exact pb.contra.map_in_R (f' a') (pb.contra.map (f' a')) rfl
      R_in_map := fun f' f r => funext fun a => by
        have hra : pa.R a (pa.cov.map a) := pa.cov.map_in_R a (pa.cov.map a) rfl
        exact pb.contra.R_in_map _ _ (r a (pa.cov.map a) hra) }

end Samples

/- ===================== the graded arrow family ===================== -/
/-- the covariant half `MapHas m (RArrow RA RB)` from A's contra + B's cov (one arm per class). -/
def arrowCov {A B A' B' : Type u} :
    (m : MapClass) → MapClass.le m map3 = true →
    (pa : Param.{u,v} (mapDepArrow m).1.1 (mapDepArrow m).1.2 A A') →
    (pb : Param.{u,v} (mapDepArrow m).2.1 (mapDepArrow m).2.2 B B') →
    MapHas.{u, max u v} m (RArrow pa.R pb.R)
  | map0,  _,  _,  _  => ULift.up {}
  | map1,  _,  pa, pb => ULift.up { map := fun f a' => pb.cov.down.map (f (pa.contra.down.map a')) }
  | map2a, _,  pa, pb =>
      { map := fun f a' => pb.cov.map (f (pa.contra.down.map a'))
        map_in_R := fun f f' h a a' raa => by
          have ha : pa.contra.down.map a' = a := pa.contra.down.R_in_map a' a raa
          have hf : f' a' = pb.cov.map (f (pa.contra.down.map a')) := (congrFun h a').symm
          rw [hf, ha]; exact pb.cov.map_in_R (f a) (pb.cov.map (f a)) rfl }
  | map2b, _,  pa, pb =>
      ULift.up
      { map := fun f a' => pb.cov.down.map (f (pa.contra.map a'))
        R_in_map := fun f f' r => funext fun a' => by
          have hra : pa.R (pa.contra.map a') a' := pa.contra.map_in_R a' (pa.contra.map a') rfl
          exact pb.cov.down.R_in_map _ _ (r (pa.contra.map a') a' hra) }
  | map3,  _,  pa, pb =>
      { map := fun f a' => pb.cov.map (f (pa.contra.map a'))
        map_in_R := fun f f' h a a' raa => by
          have ha : pa.contra.map a' = a := pa.contra.R_in_map a' a raa
          have hf : f' a' = pb.cov.map (f (pa.contra.map a')) := (congrFun h a').symm
          rw [hf, ha]; exact pb.cov.map_in_R (f a) (pb.cov.map (f a)) rfl
        R_in_map := fun f f' r => funext fun a' => by
          have hra : pa.R (pa.contra.map a') a' := pa.contra.map_in_R a' (pa.contra.map a') rfl
          exact pb.cov.R_in_map _ _ (r (pa.contra.map a') a' hra) }
  | map4,  hm, _,  _  => nomatch hm

/-- the contravariant half `MapHas n (sym (RArrow RA RB))` from A's cov + B's contra (the mirror). -/
def arrowContra {A B A' B' : Type u} :
    (n : MapClass) → MapClass.le n map3 = true →
    (pa : Param.{u,v} (mapDepArrow n).1.2 (mapDepArrow n).1.1 A A') →
    (pb : Param.{u,v} (mapDepArrow n).2.2 (mapDepArrow n).2.1 B B') →
    MapHas.{u, max u v} n (fun (f' : A' → B') (f : A → B) => RArrow pa.R pb.R f f')
  | map0,  _,  _,  _  => ULift.up {}
  | map1,  _,  pa, pb => ULift.up { map := fun f' a => pb.contra.down.map (f' (pa.cov.down.map a)) }
  | map2a, _,  pa, pb =>
      { map := fun f' a => pb.contra.map (f' (pa.cov.down.map a))
        map_in_R := fun f' f h a a' raa => by
          have ha : pa.cov.down.map a = a' := pa.cov.down.R_in_map a a' raa
          have hf : f a = pb.contra.map (f' (pa.cov.down.map a)) := (congrFun h a).symm
          rw [hf, ha]; exact pb.contra.map_in_R (f' a') (pb.contra.map (f' a')) rfl }
  | map2b, _,  pa, pb =>
      ULift.up
      { map := fun f' a => pb.contra.down.map (f' (pa.cov.map a))
        R_in_map := fun f' f r => funext fun a => by
          have hra : pa.R a (pa.cov.map a) := pa.cov.map_in_R a (pa.cov.map a) rfl
          exact pb.contra.down.R_in_map _ _ (r a (pa.cov.map a) hra) }
  | map3,  _,  pa, pb =>
      { map := fun f' a => pb.contra.map (f' (pa.cov.map a))
        map_in_R := fun f' f h a a' raa => by
          have ha : pa.cov.map a = a' := pa.cov.R_in_map a a' raa
          have hf : f a = pb.contra.map (f' (pa.cov.map a)) := (congrFun h a).symm
          rw [hf, ha]; exact pb.contra.map_in_R (f' a') (pb.contra.map (f' a')) rfl
        R_in_map := fun f' f r => funext fun a => by
          have hra : pa.R a (pa.cov.map a) := pa.cov.map_in_R a (pa.cov.map a) rfl
          exact pb.contra.R_in_map _ _ (r a (pa.cov.map a) hra) }
  | map4,  hn, _,  _  => nomatch hn

/-- arrow at ANY output class `(m,n)` with `m,n ≤ 3`, from parts at the `depArrow`-minimal classes.
    The single joined-class part is weakened down to what each half (cov/contra) consumes; every
    weakening obligation is `join ≥ component`, discharged by `cases m <;> cases n <;> rfl`. -/
def paramArrow {A B A' B' : Type u} (m n : MapClass)
    (hm : MapClass.le m map3 = true) (hn : MapClass.le n map3 = true)
    (pa : Param.{u,v} (depArrow (m, n)).1.1 (depArrow (m, n)).1.2 A A')
    (pb : Param.{u,v} (depArrow (m, n)).2.1 (depArrow (m, n)).2.2 B B') :
    Param.{u, max u v} m n (A → B) (A' → B') where
  R := RArrow pa.R pb.R
  cov := arrowCov m hm
    ((pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param.{u,v} (mapDepArrow m).1.1 (mapDepArrow m).1.2 A A')
    ((pb.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param.{u,v} (mapDepArrow m).2.1 (mapDepArrow m).2.2 B B')
  contra := arrowContra n hn
    ((pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param.{u,v} (mapDepArrow n).1.2 (mapDepArrow n).1.1 A A')
    ((pb.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param.{u,v} (mapDepArrow n).2.2 (mapDepArrow n).2.1 B B')

end Trocq
