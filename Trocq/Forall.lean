/-
Graded combinator family, stage 2: the dependent Π combinator `paramForall`.

The dependent generalization of `paramArrow`: the codomain is a FAMILY `B : A → Type`, and the
relation between codomains is itself indexed by the domain relatedness,
  `RB : ∀ a a', RA a a' → B a → B' a' → Type`,
so the Π-relation is `RForall f f' := ∀ a a' (raa : RA a a'), RB a a' raa (f a) (f' a')`.

THE WRINKLE (why Π ≠ arrow): to land in `RB a a' raa` the forward map must *produce* a relatedness
proof `raa` for the backward map — i.e. the domain's backward map must be RELATED, not just a function.
That is exactly what `mapDepPi` encodes: its domain classes are higher than `mapDepArrow`'s. Output cov
`2a`/`3` even demand the domain at `map4` *with* the adjoint coherence `R_in_mapK` (deferred, like
arrow's `map4`). The coherence-FREE frontier for Π is thus output components `≤ 2b`; we cap there
(`le · map2b`), covering `{0,1,2b}²` — the function/section directions of dependent transport.
-/
import Trocq.Arrow
universe u v
namespace Trocq
open MapClass

/- ===================== the dependent Π relation ===================== -/
/-- related inputs ↦ related outputs, where the output relation depends on the input relatedness. -/
def RForall {A A' : Type u} {B : A → Type u} {B' : A' → Type u}
    (RA : A → A' → Type v) (RB : ∀ a a', RA a a' → B a → B' a' → Type v) :
    (∀ a, B a) → (∀ a', B' a') → Type (max u v) :=
  fun f f' => ∀ a a' (raa : RA a a'), RB a a' raa (f a) (f' a')

/- ===================== the covariant half (output cov class ≤ 2b) ===================== -/
def forallCov {A A' : Type u} {B : A → Type u} {B' : A' → Type u} :
    (m : MapClass) → MapClass.le m map2b = true →
    (pa : Param.{u,v} (mapDepPi m).1.1 (mapDepPi m).1.2 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param.{u,v} (mapDepPi m).2.1 (mapDepPi m).2.2 (B a) (B' a')) →
    MapHas.{u, max u v} m (RForall pa.R (fun a a' raa => (pb a a' raa).R))
  | map0,  _,  _,  _  => ULift.up {}
  | map1,  _,  pa, pb => ULift.up
      { map := fun f a' =>
          (pb (pa.contra.map a') a' (pa.contra.map_in_R a' (pa.contra.map a') rfl)).cov.down.map
            (f (pa.contra.map a')) }
  | map2b, _,  pa, pb => ULift.up
      { map := fun f a' =>
          (pb (pa.contra.map a') a' (pa.contra.map_in_R a' (pa.contra.map a') rfl)).cov.down.map
            (f (pa.contra.map a'))
        R_in_map := fun _f _f' r => funext fun a' =>
          let raa := pa.contra.map_in_R a' (pa.contra.map a') rfl
          (pb (pa.contra.map a') a' raa).cov.down.R_in_map _ _ (r (pa.contra.map a') a' raa) }
  | map2a, h,  _,  _  => nomatch h
  | map3,  h,  _,  _  => nomatch h
  | map4,  h,  _,  _  => nomatch h

/- ===================== the contravariant half (output contra class ≤ 2b) ===================== -/
def forallContra {A A' : Type u} {B : A → Type u} {B' : A' → Type u} :
    (n : MapClass) → MapClass.le n map2b = true →
    (pa : Param.{u,v} (mapDepPi n).1.2 (mapDepPi n).1.1 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param.{u,v} (mapDepPi n).2.2 (mapDepPi n).2.1 (B a) (B' a')) →
    MapHas.{u, max u v} n (fun (f' : ∀ a', B' a') (f : ∀ a, B a) =>
      RForall pa.R (fun a a' raa => (pb a a' raa).R) f f')
  | map0,  _,  _,  _  => ULift.up {}
  | map1,  _,  pa, pb => ULift.up
      { map := fun f' a =>
          (pb a (pa.cov.map a) (pa.cov.map_in_R a (pa.cov.map a) rfl)).contra.down.map
            (f' (pa.cov.map a)) }
  | map2b, _,  pa, pb => ULift.up
      { map := fun f' a =>
          (pb a (pa.cov.map a) (pa.cov.map_in_R a (pa.cov.map a) rfl)).contra.down.map
            (f' (pa.cov.map a))
        R_in_map := fun _f' _f r => funext fun a =>
          let raa := pa.cov.map_in_R a (pa.cov.map a) rfl
          (pb a (pa.cov.map a) raa).contra.down.R_in_map _ _ (r a (pa.cov.map a) raa) }
  | map2a, h,  _,  _  => nomatch h
  | map3,  h,  _,  _  => nomatch h
  | map4,  h,  _,  _  => nomatch h

/- ===================== the graded dependent-Π combinator (output ≤ (2b,2b)) ===================== -/
/-- dependent Π at any output class `(m,n)` with `m,n ≤ 2b`, from a domain witness and a codomain
    FAMILY (one witness per related pair), each at the `depPi`-minimal class. -/
def paramForall {A A' : Type u} {B : A → Type u} {B' : A' → Type u} (m n : MapClass)
    (hm : MapClass.le m map2b = true) (hn : MapClass.le n map2b = true)
    (pa : Param.{u,v} (depPi (m, n)).1.1 (depPi (m, n)).1.2 A A')
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param.{u,v} (depPi (m, n)).2.1 (depPi (m, n)).2.2 (B a) (B' a')) :
    Param.{u, max u v} m n (∀ a, B a) (∀ a', B' a') where
  R := RForall pa.R (fun a a' raa => (pb a a' raa).R)
  cov := forallCov m hm
    ((pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param.{u,v} (mapDepPi m).1.1 (mapDepPi m).1.2 A A')
    (fun a a' raa => ((pb a a' raa).weaken (by cases m <;> cases n <;> rfl)
        (by cases m <;> cases n <;> rfl) :
      Param.{u,v} (mapDepPi m).2.1 (mapDepPi m).2.2 (B a) (B' a')))
  contra := forallContra n hn
    ((pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param.{u,v} (mapDepPi n).1.2 (mapDepPi n).1.1 A A')
    (fun a a' raa => ((pb a a' raa).weaken (by cases m <;> cases n <;> rfl)
        (by cases m <;> cases n <;> rfl) :
      Param.{u,v} (mapDepPi n).2.2 (mapDepPi n).2.1 (B a) (B' a')))

end Trocq
