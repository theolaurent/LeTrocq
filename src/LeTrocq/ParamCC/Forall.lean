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
proof `raa` for the backward map — the domain's backward map must be RELATED. `mapForallVariance` encodes this:
at output cov `2a`+ the domain is needed at `map4`; then `R_in_map` gives `bwd a' = a` (so `subst`
transports the codomain fiber) and `Map4Has.subsingleton` identifies the two relatedness proofs.
-/
import LeTrocq.Hierarchy
universe u w v vb
namespace LeTrocq
open MapClass

/- ===================== the dependent Π relation ===================== -/
/-- related inputs ↦ related outputs, where the output relation depends on the input relatedness. -/
def RForall {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w}
    (RA : A → A' → Type v) (RB : ∀ a a', RA a a' → B a → B' a' → Type vb) :
    (∀ a, B a) → (∀ a', B' a') → Type (max u v vb) :=
  fun f f' => ∀ a a' (raa : RA a a'), RB a a' raa (f a) (f' a')

/- ===================== the Π GRADING table (output class → minimal part classes) ===================== -/
/-- per-map-class minimal (domain, codomain) classes for a dependent Π (verbatim from Trocq's `class.elpi`);
    the Π domain needs the FULL equivalence at cov ≥ 2a (the `(0,4)` entries) — the wrinkle above. -/
def mapForallVariance : MapClass → (ParamClass × ParamClass)
  | map0  => ((map0,map0), (map0,map0))
  | map1  => ((map0,map2a),(map1,map0))
  | map2a => ((map0,map4), (map2a,map0))
  | map2b => ((map0,map2a),(map2b,map0))
  | map3  => ((map0,map4), (map3,map0))
  | map4  => ((map0,map4), (map4,map0))

/-- minimal (domain-class, codomain-class) needed to build the Π at output class `c`: the cov requirement joined
    with the negated contra one. `Transfer.assemble` inverts a demand through this to grade the parts;
    `paramForall`'s type consumes it. -/
def forallVariance (c : ParamClass) : ParamClass × ParamClass :=
  let (am, bm) := mapForallVariance c.1
  let (an, bn) := mapForallVariance c.2
  (ParamClass.join am (ParamClass.negate an), ParamClass.join bm (ParamClass.negate bn))

/- ===================== the covariant half ===================== -/
/- The shared covariant obligations, written ONCE and reused across the arms via the family's RAW projected
   maps (`bmap`/`bMapInR`/`bRInMap` = `fun a a' raa => (pb a a' raa).cov.…`), so no `Param` is weakened (which
   would bury the map). `pcMap`/`pcMapInR`/… are A-side `pa.contra` fields. -/
def forallCovMap {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w} {RA : A → A' → Type v}
    (pcMap : A' → A) (pcMapInR : ∀ a' a, pcMap a' = a → RA a a')
    (bmap : ∀ a a', RA a a' → B a → B' a') : (∀ a, B a) → ∀ a', B' a' :=
  fun f a' => bmap (pcMap a') a' (pcMapInR a' (pcMap a') rfl) (f (pcMap a'))

def forallCovMapInR {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w} {RA : A → A' → Type v}
    {pbR : ∀ a a', RA a a' → B a → B' a' → Type vb}
    (pcMap : A' → A) (pcRInMap : ∀ a' a, RA a a' → pcMap a' = a)
    (pcMapInR : ∀ a' a, pcMap a' = a → RA a a') (pcSub : ∀ a' a, Subsingleton (RA a a'))
    (bmap : ∀ a a', RA a a' → B a → B' a')
    (bMapInR : ∀ a a' (raa : RA a a') x y, bmap a a' raa x = y → pbR a a' raa x y) :
    ∀ f f', forallCovMap pcMap pcMapInR bmap f = f' → RForall RA pbR f f' := by
  intro f f' h a a' raa
  have hbwd : pcMap a' = a := pcRInMap a' a raa
  subst hbwd
  haveI : Subsingleton (RA (pcMap a') a') := pcSub a' (pcMap a')
  have hraa : raa = pcMapInR a' (pcMap a') rfl := Subsingleton.elim _ _
  have hf : f' a' = bmap (pcMap a') a' (pcMapInR a' (pcMap a') rfl) (f (pcMap a')) := (congrFun h a').symm
  rw [hraa, hf]
  exact bMapInR (pcMap a') a' (pcMapInR a' (pcMap a') rfl) (f (pcMap a')) _ rfl

theorem forallCovRInMap {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w} {RA : A → A' → Type v}
    {pbR : ∀ a a', RA a a' → B a → B' a' → Type vb}
    (pcMap : A' → A) (pcMapInR : ∀ a' a, pcMap a' = a → RA a a')
    (bmap : ∀ a a', RA a a' → B a → B' a')
    (bRInMap : ∀ a a' (raa : RA a a') x y, pbR a a' raa x y → bmap a a' raa x = y) :
    ∀ f f', RForall RA pbR f f' → forallCovMap pcMap pcMapInR bmap f = f' :=
  fun _f _f' r => funext fun a' =>
    let raa := pcMapInR a' (pcMap a') rfl
    bRInMap (pcMap a') a' raa _ _ (r (pcMap a') a' raa)

/-- the Π relation is a subsingleton when every fiber relation is (at `map4`), so the coherence is free. -/
theorem RForall.allEq {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w} {RA : A → A' → Type v}
    {pbR : ∀ a a', RA a a' → B a → B' a' → Type vb}
    (hB : ∀ a a' raa x y, Subsingleton (pbR a a' raa x y)) {f f'} (x y : RForall RA pbR f f') : x = y :=
  funext fun a => funext fun a' => funext fun raa => @Subsingleton.elim _ (hB a a' raa (f a) (f' a')) _ _

def forallCov {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w} :
    (m : MapClass) →
    (pa : Param (mapForallVariance m).1.1 (mapForallVariance m).1.2 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapForallVariance m).2.1 (mapForallVariance m).2.2 (B a) (B' a')) →
    MapHas m (RForall pa.R (fun a a' raa => (pb a a' raa).R))
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := forallCovMap pa.contra.map pa.contra.map_in_R (fun a a' raa => (pb a a' raa).cov.map) }
  | map2a, pa, pb => { map := forallCovMap pa.contra.map pa.contra.map_in_R (fun a a' raa => (pb a a' raa).cov.map),
                       map_in_R := forallCovMapInR pa.contra.map pa.contra.R_in_map pa.contra.map_in_R
                         pa.contra.subsingleton (fun a a' raa => (pb a a' raa).cov.map)
                         (fun a a' raa => (pb a a' raa).cov.map_in_R) }
  | map2b, pa, pb => { map := forallCovMap pa.contra.map pa.contra.map_in_R (fun a a' raa => (pb a a' raa).cov.map),
                       R_in_map := forallCovRInMap pa.contra.map pa.contra.map_in_R
                         (fun a a' raa => (pb a a' raa).cov.map) (fun a a' raa => (pb a a' raa).cov.R_in_map) }
  | map3,  pa, pb => { map := forallCovMap pa.contra.map pa.contra.map_in_R (fun a a' raa => (pb a a' raa).cov.map),
                       map_in_R := forallCovMapInR pa.contra.map pa.contra.R_in_map pa.contra.map_in_R
                         pa.contra.subsingleton (fun a a' raa => (pb a a' raa).cov.map)
                         (fun a a' raa => (pb a a' raa).cov.map_in_R),
                       R_in_map := forallCovRInMap pa.contra.map pa.contra.map_in_R
                         (fun a a' raa => (pb a a' raa).cov.map) (fun a a' raa => (pb a a' raa).cov.R_in_map) }
  | map4,  pa, pb => { map := forallCovMap pa.contra.map pa.contra.map_in_R (fun a a' raa => (pb a a' raa).cov.map),
                       map_in_R := forallCovMapInR pa.contra.map pa.contra.R_in_map pa.contra.map_in_R
                         pa.contra.subsingleton (fun a a' raa => (pb a a' raa).cov.map)
                         (fun a a' raa => (pb a a' raa).cov.map_in_R),
                       R_in_map := forallCovRInMap pa.contra.map pa.contra.map_in_R
                         (fun a a' raa => (pb a a' raa).cov.map) (fun a a' raa => (pb a a' raa).cov.R_in_map),
                       R_in_mapK := fun _ _ _ =>
                         RForall.allEq (fun a a' raa x y => (pb a a' raa).cov.subsingleton x y) _ _ }

/- ===================== the contravariant half ===================== -/
/- the contra mirror of the cov helpers: A-side uses `pa.cov` (`pcMap : A → A'`), the fiber uses `pb.contra`
   (`bmap : … → B' a' → B a`). Same raw-projection technique. -/
def forallContraMap {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w} {RA : A → A' → Type v}
    (pcMap : A → A') (pcMapInR : ∀ a a', pcMap a = a' → RA a a')
    (bmap : ∀ a a', RA a a' → B' a' → B a) : (∀ a', B' a') → ∀ a, B a :=
  fun f' a => bmap a (pcMap a) (pcMapInR a (pcMap a) rfl) (f' (pcMap a))

def forallContraMapInR {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w} {RA : A → A' → Type v}
    {pbR : ∀ a a', RA a a' → B a → B' a' → Type vb}
    (pcMap : A → A') (pcRInMap : ∀ a a', RA a a' → pcMap a = a')
    (pcMapInR : ∀ a a', pcMap a = a' → RA a a') (pcSub : ∀ a a', Subsingleton (RA a a'))
    (bmap : ∀ a a', RA a a' → B' a' → B a)
    (bMapInR : ∀ a a' (raa : RA a a') y x, bmap a a' raa y = x → pbR a a' raa x y) :
    ∀ f' f, forallContraMap pcMap pcMapInR bmap f' = f → RForall RA pbR f f' := by
  intro f' f h a a' raa
  have hfwd : pcMap a = a' := pcRInMap a a' raa
  subst hfwd
  haveI : Subsingleton (RA a (pcMap a)) := pcSub a (pcMap a)
  have hraa : raa = pcMapInR a (pcMap a) rfl := Subsingleton.elim _ _
  have hf : f a = bmap a (pcMap a) (pcMapInR a (pcMap a) rfl) (f' (pcMap a)) := (congrFun h a).symm
  rw [hraa, hf]
  exact bMapInR a (pcMap a) (pcMapInR a (pcMap a) rfl) (f' (pcMap a)) _ rfl

theorem forallContraRInMap {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w} {RA : A → A' → Type v}
    {pbR : ∀ a a', RA a a' → B a → B' a' → Type vb}
    (pcMap : A → A') (pcMapInR : ∀ a a', pcMap a = a' → RA a a')
    (bmap : ∀ a a', RA a a' → B' a' → B a)
    (bRInMap : ∀ a a' (raa : RA a a') y x, pbR a a' raa x y → bmap a a' raa y = x) :
    ∀ f' f, RForall RA pbR f f' → forallContraMap pcMap pcMapInR bmap f' = f :=
  fun _f' _f r => funext fun a =>
    let raa := pcMapInR a (pcMap a) rfl
    bRInMap a (pcMap a) raa _ _ (r a (pcMap a) raa)

def forallContra {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w} :
    (n : MapClass) →
    (pa : Param (mapForallVariance n).1.2 (mapForallVariance n).1.1 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapForallVariance n).2.2 (mapForallVariance n).2.1 (B a) (B' a')) →
    MapHas n (fun (f' : ∀ a', B' a') (f : ∀ a, B a) =>
      RForall pa.R (fun a a' raa => (pb a a' raa).R) f f')
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := forallContraMap pa.cov.map pa.cov.map_in_R (fun a a' raa => (pb a a' raa).contra.map) }
  | map2a, pa, pb => { map := forallContraMap pa.cov.map pa.cov.map_in_R (fun a a' raa => (pb a a' raa).contra.map),
                       map_in_R := forallContraMapInR pa.cov.map pa.cov.R_in_map pa.cov.map_in_R
                         pa.cov.subsingleton (fun a a' raa => (pb a a' raa).contra.map)
                         (fun a a' raa => (pb a a' raa).contra.map_in_R) }
  | map2b, pa, pb => { map := forallContraMap pa.cov.map pa.cov.map_in_R (fun a a' raa => (pb a a' raa).contra.map),
                       R_in_map := forallContraRInMap pa.cov.map pa.cov.map_in_R
                         (fun a a' raa => (pb a a' raa).contra.map) (fun a a' raa => (pb a a' raa).contra.R_in_map) }
  | map3,  pa, pb => { map := forallContraMap pa.cov.map pa.cov.map_in_R (fun a a' raa => (pb a a' raa).contra.map),
                       map_in_R := forallContraMapInR pa.cov.map pa.cov.R_in_map pa.cov.map_in_R
                         pa.cov.subsingleton (fun a a' raa => (pb a a' raa).contra.map)
                         (fun a a' raa => (pb a a' raa).contra.map_in_R),
                       R_in_map := forallContraRInMap pa.cov.map pa.cov.map_in_R
                         (fun a a' raa => (pb a a' raa).contra.map) (fun a a' raa => (pb a a' raa).contra.R_in_map) }
  | map4,  pa, pb => { map := forallContraMap pa.cov.map pa.cov.map_in_R (fun a a' raa => (pb a a' raa).contra.map),
                       map_in_R := forallContraMapInR pa.cov.map pa.cov.R_in_map pa.cov.map_in_R
                         pa.cov.subsingleton (fun a a' raa => (pb a a' raa).contra.map)
                         (fun a a' raa => (pb a a' raa).contra.map_in_R),
                       R_in_map := forallContraRInMap pa.cov.map pa.cov.map_in_R
                         (fun a a' raa => (pb a a' raa).contra.map) (fun a a' raa => (pb a a' raa).contra.R_in_map),
                       R_in_mapK := fun _ _ _ =>
                         RForall.allEq (fun a a' raa x y => (pb a a' raa).contra.subsingleton y x) _ _ }

/- ===================== the graded dependent-Π combinator (every output class) ===================== -/
/-- dependent Π at ANY output class `(m,n)`, from a domain witness and a codomain FAMILY (one witness
    per related pair), each at the `forallVariance`-minimal class. -/
def paramForall {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w} (m n : MapClass)
    (pa : Param (forallVariance (m, n)).1.1 (forallVariance (m, n)).1.2 A A')
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (forallVariance (m, n)).2.1 (forallVariance (m, n)).2.2 (B a) (B' a')) :
    Param m n (∀ a, B a) (∀ a', B' a') where
  R := RForall pa.R (fun a a' raa => (pb a a' raa).R)
  cov := forallCov m
    ((pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param (mapForallVariance m).1.1 (mapForallVariance m).1.2 A A')
    (fun a a' raa => ((pb a a' raa).weaken (by cases m <;> cases n <;> rfl)
        (by cases m <;> cases n <;> rfl) :
      Param (mapForallVariance m).2.1 (mapForallVariance m).2.2 (B a) (B' a')))
  contra := forallContra n
    ((pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param (mapForallVariance n).1.2 (mapForallVariance n).1.1 A A')
    (fun a a' raa => ((pb a a' raa).weaken (by cases m <;> cases n <;> rfl)
        (by cases m <;> cases n <;> rfl) :
      Param (mapForallVariance n).2.2 (mapForallVariance n).2.1 (B a) (B' a')))

end LeTrocq
