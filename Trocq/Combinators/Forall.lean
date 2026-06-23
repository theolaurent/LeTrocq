/-
The dependent Π combinator `paramForall` — at EVERY output class.

The dependent generalization of `paramArrow`: the codomain is a FAMILY `B : A → Sort w`, and the
relation between codomains is itself indexed by the domain relatedness,
  `RB : ∀ a a', RA a a' → B a → B' a' → Type`,
so the Π-relation is `RForall f f' := ∀ a a' (raa : RA a a'), RB a a' raa (f a) (f' a')`.

Over `Sort` (not just `Type`): the codomain family `B : A → Sort w` may land in `Prop` (`w = 0`), so this
combinator transfers `∀ x, P x` for a `Prop`-valued `P` — `Prop` propositions are subsingletons, so the
`(4,4)` coherence is free. Universes are left to inference (they shift with `Sort`).

THE WRINKLE (why Π ≠ arrow): to land in `RB a a' raa` the forward map must *produce* a relatedness
proof `raa` for the backward map — the domain's backward map must be RELATED. `mapDepPi` encodes this:
at output cov `2a`+ the domain is needed at `map4`; then `R_in_map` gives `bwd a' = a` (so `subst`
transports the codomain fiber) and `Map4Has.subsingleton` identifies the two relatedness proofs.
-/
import Trocq.Hierarchy
universe u w v vb
namespace Trocq
open MapClass

/- ===================== the dependent Π relation ===================== -/
/-- related inputs ↦ related outputs, where the output relation depends on the input relatedness. -/
def RForall {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w}
    (RA : A → A' → Type v) (RB : ∀ a a', RA a a' → B a → B' a' → Type vb) :
    (∀ a, B a) → (∀ a', B' a') → Type (max u v vb) :=
  fun f f' => ∀ a a' (raa : RA a a'), RB a a' raa (f a) (f' a')

/- ===================== the covariant half ===================== -/
def forallCov {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w} :
    (m : MapClass) →
    (pa : Param (mapDepPi m).1.1 (mapDepPi m).1.2 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapDepPi m).2.1 (mapDepPi m).2.2 (B a) (B' a')) →
    MapHas m (RForall pa.R (fun a a' raa => (pb a a' raa).R))
  | map0,  _,  _  => {}
  | map1,  pa, pb =>
      { map := fun f a' =>
          (pb (pa.contra.map a') a' (pa.contra.map_in_R a' (pa.contra.map a') rfl)).cov.map
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
  | map2b, pa, pb =>
      { map := fun f a' =>
          (pb (pa.contra.map a') a' (pa.contra.map_in_R a' (pa.contra.map a') rfl)).cov.map
            (f (pa.contra.map a'))
        R_in_map := fun _f _f' r => funext fun a' =>
          let raa := pa.contra.map_in_R a' (pa.contra.map a') rfl
          (pb (pa.contra.map a') a' raa).cov.R_in_map _ _ (r (pa.contra.map a') a' raa) }
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
def forallContra {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w} :
    (n : MapClass) →
    (pa : Param (mapDepPi n).1.2 (mapDepPi n).1.1 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapDepPi n).2.2 (mapDepPi n).2.1 (B a) (B' a')) →
    MapHas n (fun (f' : ∀ a', B' a') (f : ∀ a, B a) =>
      RForall pa.R (fun a a' raa => (pb a a' raa).R) f f')
  | map0,  _,  _  => {}
  | map1,  pa, pb =>
      { map := fun f' a =>
          (pb a (pa.cov.map a) (pa.cov.map_in_R a (pa.cov.map a) rfl)).contra.map
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
  | map2b, pa, pb =>
      { map := fun f' a =>
          (pb a (pa.cov.map a) (pa.cov.map_in_R a (pa.cov.map a) rfl)).contra.map
            (f' (pa.cov.map a))
        R_in_map := fun _f' _f r => funext fun a =>
          let raa := pa.cov.map_in_R a (pa.cov.map a) rfl
          (pb a (pa.cov.map a) raa).contra.R_in_map _ _ (r a (pa.cov.map a) raa) }
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
def paramForall {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w} (m n : MapClass)
    (pa : Param (depPi (m, n)).1.1 (depPi (m, n)).1.2 A A')
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (depPi (m, n)).2.1 (depPi (m, n)).2.2 (B a) (B' a')) :
    Param m n (∀ a, B a) (∀ a', B' a') where
  R := RForall pa.R (fun a a' raa => (pb a a' raa).R)
  cov := forallCov m
    ((pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param (mapDepPi m).1.1 (mapDepPi m).1.2 A A')
    (fun a a' raa => ((pb a a' raa).weaken (by cases m <;> cases n <;> rfl)
        (by cases m <;> cases n <;> rfl) :
      Param (mapDepPi m).2.1 (mapDepPi m).2.2 (B a) (B' a')))
  contra := forallContra n
    ((pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param (mapDepPi n).1.2 (mapDepPi n).1.1 A A')
    (fun a a' raa => ((pb a a' raa).weaken (by cases m <;> cases n <;> rfl)
        (by cases m <;> cases n <;> rfl) :
      Param (mapDepPi n).2.2 (mapDepPi n).2.1 (B a) (B' a')))

end Trocq
