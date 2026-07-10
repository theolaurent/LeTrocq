/-
The dependent Π combinator `paramForall`, at every output class. Dependent generalization of `paramArrow`:
the codomain is a family `B : A → Sort w` with codomain relation indexed by domain relatedness, so
`RForall f f' := ∀ a a' (aRel : RA a a'), RB a a' aRel (f a) (f' a')`. Over `Sort`, so `B` may land in `Prop`
and this transfers `∀ x, P x` (`Prop` subsingletons make the `(4,4)` coherence free); universes are inferred.

THE WRINKLE (why Π ≠ arrow): to land in `RB a a' aRel` the forward map must produce a relatedness proof for
the backward map, so the domain's backward map must be related. `mapForallVariance` encodes this: at output
cov `2a`+ the domain is needed at `map4`, where `rInMap` gives `bwd a' = a` (to `subst` the codomain fiber)
and `Map4Has.subsingleton` identifies the two relatedness proofs.
-/
import LeTrocq.Core.Param
universe u uA w v vb
namespace LeTrocq
open MapClass

/- ===================== the dependent Π relation ===================== -/
/-- related inputs ↦ related outputs, where the output relation depends on the input relatedness. -/
def RForall {A A' : Sort uA} {B : A → Sort w} {B' : A' → Sort w}
    (RA : A → A' → Type v) (RB : ∀ a a', RA a a' → B a → B' a' → Type vb) :
    (∀ a, B a) → (∀ a', B' a') → Sort (max uA (max (v+1) (vb+1))) :=
  fun f f' => ∀ a a' (aRel : RA a a'), RB a a' aRel (f a) (f' a')

/- ===================== the Π grading table (output class → minimal part classes) ===================== -/
/-- per-map-class minimal (domain, codomain) classes for a dependent Π (verbatim from Trocq's `class.elpi`);
    the domain needs the full equivalence at cov ≥ 2a (the `(0,4)` entries) — the wrinkle above. -/
def mapForallVariance : MapClass → (ParamClass × ParamClass)
  | map0  => ((map0,map0), (map0,map0))
  | map1  => ((map0,map2a),(map1,map0))
  | map2a => ((map0,map4), (map2a,map0))
  | map2b => ((map0,map2a),(map2b,map0))
  | map3  => ((map0,map4), (map3,map0))
  | map4  => ((map0,map4), (map4,map0))

/-- minimal (domain-class, codomain-class) to build the Π at output class `c`: cov requirement joined with
    negated contra. `Transfer.assemble` inverts a demand through this to grade the parts. -/
def forallVariance (c : ParamClass) : ParamClass × ParamClass :=
  let (am, bm) := mapForallVariance c.1
  let (an, bn) := mapForallVariance c.2
  (ParamClass.join am (ParamClass.negate an), ParamClass.join bm (ParamClass.negate bn))

/- ===================== the covariant half ===================== -/
/- Shared covariant obligations, written once and reused across the arms via the family's raw projected maps
   (`fun a a' aRel => (pb a a' aRel).cov.…`), so no `Param` is weakened (which would bury the map). -/
def forallCovMap {A A' : Sort uA} {B : A → Sort w} {B' : A' → Sort w} {RA : A → A' → Type v}
    (mapA : A' → A) (mapAInR : ∀ a' a, mapA a' = a → RA a a')
    (mapB : ∀ a a', RA a a' → B a → B' a') : (∀ a, B a) → ∀ a', B' a' :=
  fun f a' => mapB (mapA a') a' (mapAInR a' (mapA a') rfl) (f (mapA a'))

def forallCovMapInR {A A' : Sort uA} {B : A → Sort w} {B' : A' → Sort w} {RA : A → A' → Type v}
    {famR : ∀ a a', RA a a' → B a → B' a' → Type vb}
    (mapA : A' → A) (mapARInMap : ∀ a' a, RA a a' → mapA a' = a)
    (mapAInR : ∀ a' a, mapA a' = a → RA a a') (mapASub : ∀ a' a, Subsingleton (RA a a'))
    (mapB : ∀ a a', RA a a' → B a → B' a')
    (mapBInR : ∀ a a' (aRel : RA a a') x y, mapB a a' aRel x = y → famR a a' aRel x y) :
    ∀ f f', forallCovMap mapA mapAInR mapB f = f' → RForall RA famR f f' := by
  intro f f' h a a' aRel
  have hbwd : mapA a' = a := mapARInMap a' a aRel
  subst hbwd
  haveI : Subsingleton (RA (mapA a') a') := mapASub a' (mapA a')
  have hraa : aRel = mapAInR a' (mapA a') rfl := Subsingleton.elim _ _
  have hf : f' a' = mapB (mapA a') a' (mapAInR a' (mapA a') rfl) (f (mapA a')) := (congrFun h a').symm
  rw [hraa, hf]
  exact mapBInR (mapA a') a' (mapAInR a' (mapA a') rfl) (f (mapA a')) _ rfl

theorem forallCovRInMap {A A' : Sort uA} {B : A → Sort w} {B' : A' → Sort w} {RA : A → A' → Type v}
    {famR : ∀ a a', RA a a' → B a → B' a' → Type vb}
    (mapA : A' → A) (mapAInR : ∀ a' a, mapA a' = a → RA a a')
    (mapB : ∀ a a', RA a a' → B a → B' a')
    (mapBRInMap : ∀ a a' (aRel : RA a a') x y, famR a a' aRel x y → mapB a a' aRel x = y) :
    ∀ f f', RForall RA famR f f' → forallCovMap mapA mapAInR mapB f = f' :=
  fun _f _f' r => funext fun a' =>
    let aRel := mapAInR a' (mapA a') rfl
    mapBRInMap (mapA a') a' aRel _ _ (r (mapA a') a' aRel)

/-- the Π relation is a subsingleton when every fiber relation is (at `map4`), so the coherence is free. -/
theorem RForall.allEq {A A' : Sort uA} {B : A → Sort w} {B' : A' → Sort w} {RA : A → A' → Type v}
    {famR : ∀ a a', RA a a' → B a → B' a' → Type vb}
    (hB : ∀ a a' aRel x y, Subsingleton (famR a a' aRel x y)) {f f'} (x y : RForall RA famR f f') : x = y :=
  funext fun a => funext fun a' => funext fun aRel => @Subsingleton.elim _ (hB a a' aRel (f a) (f' a')) _ _

def forallCov {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w} :
    (m : MapClass) →
    (pa : Param (mapForallVariance m).1.1 (mapForallVariance m).1.2 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapForallVariance m).2.1 (mapForallVariance m).2.2 (B a) (B' a')) →
    MapHas m (RForall pa.R (fun a a' aRel => (pb a a' aRel).R))
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := forallCovMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).cov.map) }
  | map2a, pa, pb => { map := forallCovMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).cov.map),
                       mapInR := forallCovMapInR pa.contra.map pa.contra.rInMap pa.contra.mapInR
                         pa.contra.subsingleton (fun a a' aRel => (pb a a' aRel).cov.map)
                         (fun a a' aRel => (pb a a' aRel).cov.mapInR) }
  | map2b, pa, pb => { map := forallCovMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).cov.map),
                       rInMap := forallCovRInMap pa.contra.map pa.contra.mapInR
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.rInMap) }
  | map3,  pa, pb => { map := forallCovMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).cov.map),
                       mapInR := forallCovMapInR pa.contra.map pa.contra.rInMap pa.contra.mapInR
                         pa.contra.subsingleton (fun a a' aRel => (pb a a' aRel).cov.map)
                         (fun a a' aRel => (pb a a' aRel).cov.mapInR),
                       rInMap := forallCovRInMap pa.contra.map pa.contra.mapInR
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.rInMap) }
  | map4,  pa, pb => { map := forallCovMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).cov.map),
                       mapInR := forallCovMapInR pa.contra.map pa.contra.rInMap pa.contra.mapInR
                         pa.contra.subsingleton (fun a a' aRel => (pb a a' aRel).cov.map)
                         (fun a a' aRel => (pb a a' aRel).cov.mapInR),
                       rInMap := forallCovRInMap pa.contra.map pa.contra.mapInR
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.rInMap),
                       rInMapK := fun _ _ _ =>
                         RForall.allEq (fun a a' aRel x y => (pb a a' aRel).cov.subsingleton x y) _ _ }

/- ===================== the contravariant half ===================== -/
/- Mirror of the cov helpers: A-side uses `pa.cov`, the fiber uses `pb.contra`. Same raw-projection technique. -/
def forallContraMap {A A' : Sort uA} {B : A → Sort w} {B' : A' → Sort w} {RA : A → A' → Type v}
    (mapA : A → A') (mapAInR : ∀ a a', mapA a = a' → RA a a')
    (mapB : ∀ a a', RA a a' → B' a' → B a) : (∀ a', B' a') → ∀ a, B a :=
  fun f' a => mapB a (mapA a) (mapAInR a (mapA a) rfl) (f' (mapA a))

def forallContraMapInR {A A' : Sort uA} {B : A → Sort w} {B' : A' → Sort w} {RA : A → A' → Type v}
    {famR : ∀ a a', RA a a' → B a → B' a' → Type vb}
    (mapA : A → A') (mapARInMap : ∀ a a', RA a a' → mapA a = a')
    (mapAInR : ∀ a a', mapA a = a' → RA a a') (mapASub : ∀ a a', Subsingleton (RA a a'))
    (mapB : ∀ a a', RA a a' → B' a' → B a)
    (mapBInR : ∀ a a' (aRel : RA a a') y x, mapB a a' aRel y = x → famR a a' aRel x y) :
    ∀ f' f, forallContraMap mapA mapAInR mapB f' = f → RForall RA famR f f' := by
  intro f' f h a a' aRel
  have hfwd : mapA a = a' := mapARInMap a a' aRel
  subst hfwd
  haveI : Subsingleton (RA a (mapA a)) := mapASub a (mapA a)
  have hraa : aRel = mapAInR a (mapA a) rfl := Subsingleton.elim _ _
  have hf : f a = mapB a (mapA a) (mapAInR a (mapA a) rfl) (f' (mapA a)) := (congrFun h a).symm
  rw [hraa, hf]
  exact mapBInR a (mapA a) (mapAInR a (mapA a) rfl) (f' (mapA a)) _ rfl

theorem forallContraRInMap {A A' : Sort uA} {B : A → Sort w} {B' : A' → Sort w} {RA : A → A' → Type v}
    {famR : ∀ a a', RA a a' → B a → B' a' → Type vb}
    (mapA : A → A') (mapAInR : ∀ a a', mapA a = a' → RA a a')
    (mapB : ∀ a a', RA a a' → B' a' → B a)
    (mapBRInMap : ∀ a a' (aRel : RA a a') y x, famR a a' aRel x y → mapB a a' aRel y = x) :
    ∀ f' f, RForall RA famR f f' → forallContraMap mapA mapAInR mapB f' = f :=
  fun _f' _f r => funext fun a =>
    let aRel := mapAInR a (mapA a) rfl
    mapBRInMap a (mapA a) aRel _ _ (r a (mapA a) aRel)

def forallContra {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w} :
    (n : MapClass) →
    (pa : Param (mapForallVariance n).1.2 (mapForallVariance n).1.1 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapForallVariance n).2.2 (mapForallVariance n).2.1 (B a) (B' a')) →
    MapHas n (fun (f' : ∀ a', B' a') (f : ∀ a, B a) =>
      RForall pa.R (fun a a' aRel => (pb a a' aRel).R) f f')
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := forallContraMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).contra.map) }
  | map2a, pa, pb => { map := forallContraMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).contra.map),
                       mapInR := forallContraMapInR pa.cov.map pa.cov.rInMap pa.cov.mapInR
                         pa.cov.subsingleton (fun a a' aRel => (pb a a' aRel).contra.map)
                         (fun a a' aRel => (pb a a' aRel).contra.mapInR) }
  | map2b, pa, pb => { map := forallContraMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).contra.map),
                       rInMap := forallContraRInMap pa.cov.map pa.cov.mapInR
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.rInMap) }
  | map3,  pa, pb => { map := forallContraMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).contra.map),
                       mapInR := forallContraMapInR pa.cov.map pa.cov.rInMap pa.cov.mapInR
                         pa.cov.subsingleton (fun a a' aRel => (pb a a' aRel).contra.map)
                         (fun a a' aRel => (pb a a' aRel).contra.mapInR),
                       rInMap := forallContraRInMap pa.cov.map pa.cov.mapInR
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.rInMap) }
  | map4,  pa, pb => { map := forallContraMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).contra.map),
                       mapInR := forallContraMapInR pa.cov.map pa.cov.rInMap pa.cov.mapInR
                         pa.cov.subsingleton (fun a a' aRel => (pb a a' aRel).contra.map)
                         (fun a a' aRel => (pb a a' aRel).contra.mapInR),
                       rInMap := forallContraRInMap pa.cov.map pa.cov.mapInR
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.rInMap),
                       rInMapK := fun _ _ _ =>
                         RForall.allEq (fun a a' aRel x y => (pb a a' aRel).contra.subsingleton y x) _ _ }

/- ===================== the graded dependent-Π combinator (every output class) ===================== -/
/-- dependent Π at ANY output class `(m,n)`, from a domain witness and a codomain FAMILY (one witness
    per related pair), each at the `forallVariance`-minimal class. -/
def paramForall {A A' : Type u} {B : A → Sort w} {B' : A' → Sort w} (m n : MapClass)
    (pa : Param (forallVariance (m, n)).1.1 (forallVariance (m, n)).1.2 A A')
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (forallVariance (m, n)).2.1 (forallVariance (m, n)).2.2 (B a) (B' a')) :
    Param m n (∀ a, B a) (∀ a', B' a') where
  R := RForall pa.R (fun a a' aRel => (pb a a' aRel).R)
  cov := forallCov m
    ((pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param (mapForallVariance m).1.1 (mapForallVariance m).1.2 A A')
    (fun a a' aRel => ((pb a a' aRel).weaken (by cases m <;> cases n <;> rfl)
        (by cases m <;> cases n <;> rfl) :
      Param (mapForallVariance m).2.1 (mapForallVariance m).2.2 (B a) (B' a')))
  contra := forallContra n
    ((pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param (mapForallVariance n).1.2 (mapForallVariance n).1.1 A A')
    (fun a a' aRel => ((pb a a' aRel).weaken (by cases m <;> cases n <;> rfl)
        (by cases m <;> cases n <;> rfl) :
      Param (mapForallVariance n).2.2 (mapForallVariance n).2.1 (B a) (B' a')))

/- ===================== the Prop-DOMAIN dependent-Π combinator (Tier 2) =====================
   A Π whose DOMAIN is a proposition (`∀ h : P, B h`, incl. the non-dependent `P → Q`). Verbatim mirrors of
   `forallCov`/`forallContra`/`paramForall` with the domain pinned to `Prop` (`{A A' : Prop}`) instead of
   `Type u`: only the domain sort differs, so every arm reuses the SAME Sort-generalized leaf helpers
   (`forallCovMap`, `forallCovMapInR`, …). The pin is FORCED — over a free domain universe the relation
   `RForall` is `Sort (max uA …)`, not `Type _`-expressible, so `MapHas`/`Param.R` reject it; at `Prop`
   (`uA = 0`) it collapses to `Type _`. A `Prop` domain satisfies the forall wrinkle's `map4` demand for free
   (`paramPropAt` reaches `(4,4)`), so no grading is lost by routing here. -/
def forallCovProp {A A' : Prop} {B : A → Sort w} {B' : A' → Sort w} :
    (m : MapClass) →
    (pa : Param (mapForallVariance m).1.1 (mapForallVariance m).1.2 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapForallVariance m).2.1 (mapForallVariance m).2.2 (B a) (B' a')) →
    MapHas m (RForall pa.R (fun a a' aRel => (pb a a' aRel).R))
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := forallCovMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).cov.map) }
  | map2a, pa, pb => { map := forallCovMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).cov.map),
                       mapInR := forallCovMapInR pa.contra.map pa.contra.rInMap pa.contra.mapInR
                         pa.contra.subsingleton (fun a a' aRel => (pb a a' aRel).cov.map)
                         (fun a a' aRel => (pb a a' aRel).cov.mapInR) }
  | map2b, pa, pb => { map := forallCovMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).cov.map),
                       rInMap := forallCovRInMap pa.contra.map pa.contra.mapInR
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.rInMap) }
  | map3,  pa, pb => { map := forallCovMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).cov.map),
                       mapInR := forallCovMapInR pa.contra.map pa.contra.rInMap pa.contra.mapInR
                         pa.contra.subsingleton (fun a a' aRel => (pb a a' aRel).cov.map)
                         (fun a a' aRel => (pb a a' aRel).cov.mapInR),
                       rInMap := forallCovRInMap pa.contra.map pa.contra.mapInR
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.rInMap) }
  | map4,  pa, pb => { map := forallCovMap pa.contra.map pa.contra.mapInR (fun a a' aRel => (pb a a' aRel).cov.map),
                       mapInR := forallCovMapInR pa.contra.map pa.contra.rInMap pa.contra.mapInR
                         pa.contra.subsingleton (fun a a' aRel => (pb a a' aRel).cov.map)
                         (fun a a' aRel => (pb a a' aRel).cov.mapInR),
                       rInMap := forallCovRInMap pa.contra.map pa.contra.mapInR
                         (fun a a' aRel => (pb a a' aRel).cov.map) (fun a a' aRel => (pb a a' aRel).cov.rInMap),
                       rInMapK := fun _ _ _ =>
                         RForall.allEq (fun a a' aRel x y => (pb a a' aRel).cov.subsingleton x y) _ _ }

def forallContraProp {A A' : Prop} {B : A → Sort w} {B' : A' → Sort w} :
    (n : MapClass) →
    (pa : Param (mapForallVariance n).1.2 (mapForallVariance n).1.1 A A') →
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (mapForallVariance n).2.2 (mapForallVariance n).2.1 (B a) (B' a')) →
    MapHas n (fun (f' : ∀ a', B' a') (f : ∀ a, B a) =>
      RForall pa.R (fun a a' aRel => (pb a a' aRel).R) f f')
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := forallContraMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).contra.map) }
  | map2a, pa, pb => { map := forallContraMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).contra.map),
                       mapInR := forallContraMapInR pa.cov.map pa.cov.rInMap pa.cov.mapInR
                         pa.cov.subsingleton (fun a a' aRel => (pb a a' aRel).contra.map)
                         (fun a a' aRel => (pb a a' aRel).contra.mapInR) }
  | map2b, pa, pb => { map := forallContraMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).contra.map),
                       rInMap := forallContraRInMap pa.cov.map pa.cov.mapInR
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.rInMap) }
  | map3,  pa, pb => { map := forallContraMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).contra.map),
                       mapInR := forallContraMapInR pa.cov.map pa.cov.rInMap pa.cov.mapInR
                         pa.cov.subsingleton (fun a a' aRel => (pb a a' aRel).contra.map)
                         (fun a a' aRel => (pb a a' aRel).contra.mapInR),
                       rInMap := forallContraRInMap pa.cov.map pa.cov.mapInR
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.rInMap) }
  | map4,  pa, pb => { map := forallContraMap pa.cov.map pa.cov.mapInR (fun a a' aRel => (pb a a' aRel).contra.map),
                       mapInR := forallContraMapInR pa.cov.map pa.cov.rInMap pa.cov.mapInR
                         pa.cov.subsingleton (fun a a' aRel => (pb a a' aRel).contra.map)
                         (fun a a' aRel => (pb a a' aRel).contra.mapInR),
                       rInMap := forallContraRInMap pa.cov.map pa.cov.mapInR
                         (fun a a' aRel => (pb a a' aRel).contra.map) (fun a a' aRel => (pb a a' aRel).contra.rInMap),
                       rInMapK := fun _ _ _ =>
                         RForall.allEq (fun a a' aRel x y => (pb a a' aRel).contra.subsingleton y x) _ _ }

/-- Prop-DOMAIN dependent Π at ANY output class `(m,n)`. Same shape as `paramForall`; the driver routes any
    `∀`/`→` whose domain is a proposition here (so `P → Q`, `P → A`, `∀ h : P, B h` all transfer). -/
def paramForallProp {A A' : Prop} {B : A → Sort w} {B' : A' → Sort w} (m n : MapClass)
    (pa : Param (forallVariance (m, n)).1.1 (forallVariance (m, n)).1.2 A A')
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (forallVariance (m, n)).2.1 (forallVariance (m, n)).2.2 (B a) (B' a')) :
    Param m n (∀ a, B a) (∀ a', B' a') where
  R := RForall pa.R (fun a a' aRel => (pb a a' aRel).R)
  cov := forallCovProp m
    ((pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param (mapForallVariance m).1.1 (mapForallVariance m).1.2 A A')
    (fun a a' aRel => ((pb a a' aRel).weaken (by cases m <;> cases n <;> rfl)
        (by cases m <;> cases n <;> rfl) :
      Param (mapForallVariance m).2.1 (mapForallVariance m).2.2 (B a) (B' a')))
  contra := forallContraProp n
    ((pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) :
      Param (mapForallVariance n).1.2 (mapForallVariance n).1.1 A A')
    (fun a a' aRel => ((pb a a' aRel).weaken (by cases m <;> cases n <;> rfl)
        (by cases m <;> cases n <;> rfl) :
      Param (mapForallVariance n).2.2 (mapForallVariance n).2.1 (B a) (B' a')))

end LeTrocq
