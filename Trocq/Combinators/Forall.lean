/-
Graded combinator family, stage 2: the dependent Π combinator `paramForall` — at EVERY output class.

The dependent generalization of `paramArrow`: the codomain is a FAMILY `B : A → Type`, and the
relation between codomains is itself indexed by the domain relatedness,
  `RB : ∀ a a', RA a a' → B a → B' a' → Type`,
so the Π-relation is `RForall f f' := ∀ a a' (raa : RA a a'), RB a a' raa (f a) (f' a')`.

Four universes, all independent — essential for the flagship `∀ A : Type, A → A`:
  `u`  the domain `A : Type u`,  `w`  the codomain `B : A → Type w`,
  `v`  the domain relation `RA : Type v`,  `vb` the codomain relation `RB : Type vb`.

THE WRINKLE (why Π ≠ arrow): to land in `RB a a' raa` the forward map must *produce* a relatedness
proof `raa` for the backward map — i.e. the domain's backward map must be RELATED. `mapDepPi` encodes
this: at output cov `2a`+ the domain is needed at `map4` (a full equivalence). With the domain at `map4`
the soundness field `map_in_R` becomes provable: `R_in_map` gives `bwd a' = a` (so `subst` transports the
codomain fiber), and `Map4Has.subsingleton` identifies the two relatedness proofs of the indexed fiber.
The `(4,4)` coherence `R_in_mapK` is then free (the Π-relation of subsingletons is a subsingleton).

(Note: a Π *over `Type`* — `∀ A : Type, …` — is still capped at `(2b,2b)` by the DRIVER, because there
the domain witness is the universe combinator, which is capped at `2a` by univalence. The cap there is
on the universe, not on this combinator, which is fully graded.)
-/
import Trocq.Hierarchy
universe u w v vb
namespace Trocq
open MapClass

/- ===================== the dependent Π relation ===================== -/
/-- related inputs ↦ related outputs, where the output relation depends on the input relatedness. -/
def RForall {A A' : Type u} {B : A → Type w} {B' : A' → Type w}
    (RA : A → A' → Type v) (RB : ∀ a a', RA a a' → B a → B' a' → Type vb) :
    (∀ a, B a) → (∀ a', B' a') → Type (max u v vb) :=
  fun f f' => ∀ a a' (raa : RA a a'), RB a a' raa (f a) (f' a')

/- ===================== the covariant half ===================== -/
def forallCov {A A' : Type u} {B : A → Type w} {B' : A' → Type w} :
    (m : MapClass) →
    (pa : Param.{u,v} (mapDepPi m).1.1 (mapDepPi m).1.2 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param.{w,vb} (mapDepPi m).2.1 (mapDepPi m).2.2 (B a) (B' a')) →
    MapHas.{max u w, max u v vb} m (RForall pa.R (fun a a' raa => (pb a a' raa).R))
  | map0,  _,  _  => ULift.up {}
  | map1,  pa, pb => ULift.up
      { map := fun f a' =>
          (pb (pa.contra.map a') a' (pa.contra.map_in_R a' (pa.contra.map a') rfl)).cov.down.map
            (f (pa.contra.map a')) }
  | map2a, pa, pb =>
      { map := fun f a' =>
          (pb (pa.contra.map a') a' (pa.contra.map_in_R a' (pa.contra.map a') rfl)).cov.map
            (f (pa.contra.map a'))
        map_in_R := fun f f' h a a' raa => by
          have hbwd : pa.contra.map a' = a := pa.contra.R_in_map a' a raa
          subst hbwd
          haveI : Subsingleton (pa.R (pa.contra.map a') a') := pa.contra.subsingleton a' (pa.contra.map a')
          have hraa : raa = pa.contra.map_in_R a' (pa.contra.map a') rfl := Subsingleton.elim _ _
          have hf : f' a' = (pb (pa.contra.map a') a' (pa.contra.map_in_R a' (pa.contra.map a') rfl)).cov.map
              (f (pa.contra.map a')) := (congrFun h a').symm
          rw [hraa, hf]
          exact (pb (pa.contra.map a') a' (pa.contra.map_in_R a' (pa.contra.map a') rfl)).cov.map_in_R
            (f (pa.contra.map a')) _ rfl }
  | map2b, pa, pb => ULift.up
      { map := fun f a' =>
          (pb (pa.contra.map a') a' (pa.contra.map_in_R a' (pa.contra.map a') rfl)).cov.down.map
            (f (pa.contra.map a'))
        R_in_map := fun _f _f' r => funext fun a' =>
          let raa := pa.contra.map_in_R a' (pa.contra.map a') rfl
          (pb (pa.contra.map a') a' raa).cov.down.R_in_map _ _ (r (pa.contra.map a') a' raa) }
  | map3,  pa, pb =>
      { map := fun f a' =>
          (pb (pa.contra.map a') a' (pa.contra.map_in_R a' (pa.contra.map a') rfl)).cov.map
            (f (pa.contra.map a'))
        map_in_R := fun f f' h a a' raa => by
          have hbwd : pa.contra.map a' = a := pa.contra.R_in_map a' a raa
          subst hbwd
          haveI : Subsingleton (pa.R (pa.contra.map a') a') := pa.contra.subsingleton a' (pa.contra.map a')
          have hraa : raa = pa.contra.map_in_R a' (pa.contra.map a') rfl := Subsingleton.elim _ _
          have hf : f' a' = (pb (pa.contra.map a') a' (pa.contra.map_in_R a' (pa.contra.map a') rfl)).cov.map
              (f (pa.contra.map a')) := (congrFun h a').symm
          rw [hraa, hf]
          exact (pb (pa.contra.map a') a' (pa.contra.map_in_R a' (pa.contra.map a') rfl)).cov.map_in_R
            (f (pa.contra.map a')) _ rfl
        R_in_map := fun _f _f' r => funext fun a' =>
          let raa := pa.contra.map_in_R a' (pa.contra.map a') rfl
          (pb (pa.contra.map a') a' raa).cov.R_in_map _ _ (r (pa.contra.map a') a' raa) }
  | map4,  pa, pb =>
      { map := fun f a' =>
          (pb (pa.contra.map a') a' (pa.contra.map_in_R a' (pa.contra.map a') rfl)).cov.map
            (f (pa.contra.map a'))
        map_in_R := fun f f' h a a' raa => by
          have hbwd : pa.contra.map a' = a := pa.contra.R_in_map a' a raa
          subst hbwd
          haveI : Subsingleton (pa.R (pa.contra.map a') a') := pa.contra.subsingleton a' (pa.contra.map a')
          have hraa : raa = pa.contra.map_in_R a' (pa.contra.map a') rfl := Subsingleton.elim _ _
          have hf : f' a' = (pb (pa.contra.map a') a' (pa.contra.map_in_R a' (pa.contra.map a') rfl)).cov.map
              (f (pa.contra.map a')) := (congrFun h a').symm
          rw [hraa, hf]
          exact (pb (pa.contra.map a') a' (pa.contra.map_in_R a' (pa.contra.map a') rfl)).cov.map_in_R
            (f (pa.contra.map a')) _ rfl
        R_in_map := fun _f _f' r => funext fun a' =>
          let raa := pa.contra.map_in_R a' (pa.contra.map a') rfl
          (pb (pa.contra.map a') a' raa).cov.R_in_map _ _ (r (pa.contra.map a') a' raa)
        R_in_mapK := fun f f' _ => by
          haveI : Subsingleton (RForall pa.R (fun a a' raa => (pb a a' raa).R) f f') :=
            ⟨fun x y => funext fun a => funext fun a' => funext fun raa =>
              @Subsingleton.elim _ ((pb a a' raa).cov.subsingleton (f a) (f' a')) _ _⟩
          exact Subsingleton.elim _ _ }

/- ===================== the contravariant half ===================== -/
def forallContra {A A' : Type u} {B : A → Type w} {B' : A' → Type w} :
    (n : MapClass) →
    (pa : Param.{u,v} (mapDepPi n).1.2 (mapDepPi n).1.1 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param.{w,vb} (mapDepPi n).2.2 (mapDepPi n).2.1 (B a) (B' a')) →
    MapHas.{max u w, max u v vb} n (fun (f' : ∀ a', B' a') (f : ∀ a, B a) =>
      RForall pa.R (fun a a' raa => (pb a a' raa).R) f f')
  | map0,  _,  _  => ULift.up {}
  | map1,  pa, pb => ULift.up
      { map := fun f' a =>
          (pb a (pa.cov.map a) (pa.cov.map_in_R a (pa.cov.map a) rfl)).contra.down.map
            (f' (pa.cov.map a)) }
  | map2a, pa, pb =>
      { map := fun f' a =>
          (pb a (pa.cov.map a) (pa.cov.map_in_R a (pa.cov.map a) rfl)).contra.map
            (f' (pa.cov.map a))
        map_in_R := fun f' f h a a' raa => by
          have hfwd : pa.cov.map a = a' := pa.cov.R_in_map a a' raa
          subst hfwd
          haveI : Subsingleton (pa.R a (pa.cov.map a)) := pa.cov.subsingleton a (pa.cov.map a)
          have hraa : raa = pa.cov.map_in_R a (pa.cov.map a) rfl := Subsingleton.elim _ _
          have hf : f a = (pb a (pa.cov.map a) (pa.cov.map_in_R a (pa.cov.map a) rfl)).contra.map
              (f' (pa.cov.map a)) := (congrFun h a).symm
          rw [hraa, hf]
          exact (pb a (pa.cov.map a) (pa.cov.map_in_R a (pa.cov.map a) rfl)).contra.map_in_R
            (f' (pa.cov.map a)) _ rfl }
  | map2b, pa, pb => ULift.up
      { map := fun f' a =>
          (pb a (pa.cov.map a) (pa.cov.map_in_R a (pa.cov.map a) rfl)).contra.down.map
            (f' (pa.cov.map a))
        R_in_map := fun _f' _f r => funext fun a =>
          let raa := pa.cov.map_in_R a (pa.cov.map a) rfl
          (pb a (pa.cov.map a) raa).contra.down.R_in_map _ _ (r a (pa.cov.map a) raa) }
  | map3,  pa, pb =>
      { map := fun f' a =>
          (pb a (pa.cov.map a) (pa.cov.map_in_R a (pa.cov.map a) rfl)).contra.map
            (f' (pa.cov.map a))
        map_in_R := fun f' f h a a' raa => by
          have hfwd : pa.cov.map a = a' := pa.cov.R_in_map a a' raa
          subst hfwd
          haveI : Subsingleton (pa.R a (pa.cov.map a)) := pa.cov.subsingleton a (pa.cov.map a)
          have hraa : raa = pa.cov.map_in_R a (pa.cov.map a) rfl := Subsingleton.elim _ _
          have hf : f a = (pb a (pa.cov.map a) (pa.cov.map_in_R a (pa.cov.map a) rfl)).contra.map
              (f' (pa.cov.map a)) := (congrFun h a).symm
          rw [hraa, hf]
          exact (pb a (pa.cov.map a) (pa.cov.map_in_R a (pa.cov.map a) rfl)).contra.map_in_R
            (f' (pa.cov.map a)) _ rfl
        R_in_map := fun _f' _f r => funext fun a =>
          let raa := pa.cov.map_in_R a (pa.cov.map a) rfl
          (pb a (pa.cov.map a) raa).contra.R_in_map _ _ (r a (pa.cov.map a) raa) }
  | map4,  pa, pb =>
      { map := fun f' a =>
          (pb a (pa.cov.map a) (pa.cov.map_in_R a (pa.cov.map a) rfl)).contra.map
            (f' (pa.cov.map a))
        map_in_R := fun f' f h a a' raa => by
          have hfwd : pa.cov.map a = a' := pa.cov.R_in_map a a' raa
          subst hfwd
          haveI : Subsingleton (pa.R a (pa.cov.map a)) := pa.cov.subsingleton a (pa.cov.map a)
          have hraa : raa = pa.cov.map_in_R a (pa.cov.map a) rfl := Subsingleton.elim _ _
          have hf : f a = (pb a (pa.cov.map a) (pa.cov.map_in_R a (pa.cov.map a) rfl)).contra.map
              (f' (pa.cov.map a)) := (congrFun h a).symm
          rw [hraa, hf]
          exact (pb a (pa.cov.map a) (pa.cov.map_in_R a (pa.cov.map a) rfl)).contra.map_in_R
            (f' (pa.cov.map a)) _ rfl
        R_in_map := fun _f' _f r => funext fun a =>
          let raa := pa.cov.map_in_R a (pa.cov.map a) rfl
          (pb a (pa.cov.map a) raa).contra.R_in_map _ _ (r a (pa.cov.map a) raa)
        R_in_mapK := fun f' f _ => by
          haveI : Subsingleton (RForall pa.R (fun a a' raa => (pb a a' raa).R) f f') :=
            ⟨fun x y => funext fun a => funext fun a' => funext fun raa =>
              @Subsingleton.elim _ ((pb a a' raa).contra.subsingleton (f' a') (f a)) _ _⟩
          exact Subsingleton.elim _ _ }

/- ===================== the graded dependent-Π combinator (every output class) ===================== -/
/-- dependent Π at ANY output class `(m,n)`, from a domain witness and a codomain FAMILY (one witness
    per related pair), each at the `depPi`-minimal class. -/
def paramForall {A A' : Type u} {B : A → Type w} {B' : A' → Type w} (m n : MapClass)
    (pa : Param.{u,v} (depPi (m, n)).1.1 (depPi (m, n)).1.2 A A')
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param.{w,vb} (depPi (m, n)).2.1 (depPi (m, n)).2.2 (B a) (B' a')) :
    Param.{max u w, max u v vb} m n (∀ a, B a) (∀ a', B' a') where
  R := RForall pa.R (fun a a' raa => (pb a a' raa).R)
  cov := forallCov m
    ((pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param.{u,v} (mapDepPi m).1.1 (mapDepPi m).1.2 A A')
    (fun a a' raa => ((pb a a' raa).weaken (by cases m <;> cases n <;> rfl)
        (by cases m <;> cases n <;> rfl) :
      Param.{w,vb} (mapDepPi m).2.1 (mapDepPi m).2.2 (B a) (B' a')))
  contra := forallContra n
    ((pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param.{u,v} (mapDepPi n).1.2 (mapDepPi n).1.1 A A')
    (fun a a' raa => ((pb a a' raa).weaken (by cases m <;> cases n <;> rfl)
        (by cases m <;> cases n <;> rfl) :
      Param.{w,vb} (mapDepPi n).2.2 (mapDepPi n).2.1 (B a) (B' a')))

end Trocq
