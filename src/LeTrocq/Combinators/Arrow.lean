/-
The ARROW construction: `Param … (A→B) (A'→B')` from witnesses for the parts. `RArrow` is the respectful
relation (= Mathlib `Relator.LiftFun`); `mapArrowVariance`/`arrowVariance` is the grading table (output class →
minimal part classes); `paramArrow` builds the arrow at every output class incl. (4,4) (that coherence is free
by `Map4.subsingleton`). The domain stays over `Type u` but the CODOMAIN ranges over `Sort uB`, so an
`A → Prop` arrow (`Type` domain, `Prop` codomain) builds here — that is Tier 1. A `Prop`-DOMAIN arrow
(`P → Q`) instead routes through `paramForallProp` (its relation isn't `Type`-expressible over a free domain
universe, so it needs the domain pinned at `Prop`); see `Forall`.
-/
import LeTrocq.Core.Param
universe u uB v
namespace LeTrocq
open MapClass

/- ===================== the arrow relation (= Mathlib `Relator.LiftFun`) ===================== -/
/-- the respectful relation: related inputs ↦ related outputs. -/
def RArrow {A A' : Type u} {B B' : Sort uB} (RA : A → A' → Type v) (RB : B → B' → Type v) :
    (A → B) → (A' → B') → Type (max u v) :=
  fun f f' => ∀ a a', RA a a' → RB (f a) (f' a')

-- the arrow variance table: output (covariant) MapClass ↝ parameter ParamClasses
-- (faithful w.r.t. Trocq's `class.elpi`)
def mapArrowVariance : MapClass → (ParamClass × ParamClass)
  | map0  => ((map0,map0), (map0,map0))
  | map1  => ((map0,map1), (map1,map0))
  | map2a => ((map0,map2b),(map2a,map0))
  | map2b => ((map0,map2a),(map2b,map0))
  | map3  => ((map0,map3), (map3,map0))
  | map4  => ((map0,map4), (map4,map0))

-- TODO: should use Param.lean variance?
/-- minimal (domain-class, codomain-class) to build the arrow at output class `c`: cov requirement joined with
    negated contra. `Transfer.assemble` inverts a demand through this to grade the parts. -/
def arrowVariance (c : ParamClass) : ParamClass × ParamClass :=
  let (am, bm) := mapArrowVariance c.1
  let (an, bn) := mapArrowVariance c.2
  (ParamClass.join am (ParamClass.negate an), ParamClass.join bm (ParamClass.negate bn))

/- ===================== the graded arrow family (every output class, incl. (4,4)) ===================== -/
/- Lifted arrow soundness/completeness obligations, each written once and shared across the 2a/3/4 (resp.
   2b/3/4) arms. cov and contra are mirrors (cov via `pb.cov`, contra via `pb.contra`). -/
def arrowCovMapInR {A A' : Type u} {B B' : Sort uB} {RA : A → A' → Type v} {RB : B → B' → Type v}
    (mapA : A' → A) (mapARInMap : ∀ a' a, RA a a' → mapA a' = a)
    (mapB : B → B') (mapBInR : ∀ b b', mapB b = b' → RB b b') :
    ∀ f f', (fun a' => mapB (f (mapA a'))) = f' → RArrow RA RB f f' := by
  intro f f' h a a' aRel
  have ha : mapA a' = a := mapARInMap a' a aRel
  have hf : f' a' = mapB (f (mapA a')) := (congrFun h a').symm
  rw [hf, ha]; exact mapBInR (f a) (mapB (f a)) rfl

theorem arrowCovRInMap {A A' : Type u} {B B' : Sort uB} {RA : A → A' → Type v} {RB : B → B' → Type v}
    (mapA : A' → A) (mapAInR : ∀ a' a, mapA a' = a → RA a a')
    (mapB : B → B') (mapBRInMap : ∀ b b', RB b b' → mapB b = b') :
    ∀ f f', RArrow RA RB f f' → (fun a' => mapB (f (mapA a'))) = f' := by
  intro f f' r; funext a'
  have hra : RA (mapA a') a' := mapAInR a' (mapA a') rfl
  exact mapBRInMap _ _ (r (mapA a') a' hra)

def arrowContraMapInR {A A' : Type u} {B B' : Sort uB} {RA : A → A' → Type v} {RB : B → B' → Type v}
    (mapA : A → A') (mapARInMap : ∀ a a', RA a a' → mapA a = a')
    (mapB : B' → B) (mapBInR : ∀ b' b, mapB b' = b → RB b b') :
    ∀ f' f, (fun a => mapB (f' (mapA a))) = f → RArrow RA RB f f' := by
  intro f' f h a a' aRel
  have ha : mapA a = a' := mapARInMap a a' aRel
  have hf : f a = mapB (f' (mapA a)) := (congrFun h a).symm
  rw [hf, ha]; exact mapBInR (f' a') (mapB (f' a')) rfl

theorem arrowContraRInMap {A A' : Type u} {B B' : Sort uB} {RA : A → A' → Type v} {RB : B → B' → Type v}
    (mapA : A → A') (mapAInR : ∀ a a', mapA a = a' → RA a a')
    (mapB : B' → B) (mapBRInMap : ∀ b' b, RB b b' → mapB b' = b) :
    ∀ f' f, RArrow RA RB f f' → (fun a => mapB (f' (mapA a))) = f := by
  intro f' f r; funext a
  have hra : RA a (mapA a) := mapAInR a (mapA a) rfl
  exact mapBRInMap _ _ (r a (mapA a) hra)

/-- the arrow relation is a subsingleton when the codomain part is (at `map4`), so the coherence is free. -/
theorem RArrow.allEq {A A' : Type u} {B B' : Sort uB} {RA : A → A' → Type v} {RB : B → B' → Type v}
    (hB : ∀ b b', Subsingleton (RB b b')) {f : A → B} {f' : A' → B'} (x y : RArrow RA RB f f') : x = y :=
  funext fun a => funext fun a' => funext fun _ => @Subsingleton.elim _ (hB (f a) (f' a')) _ _

/-- the covariant half `Map m (RArrow RA RB)` from A's contra + B's cov. At `map4` the coherence is free:
    class-4 parts have subsingleton relations, so the arrow relation is too. -/
def arrowCov {A A' : Type u} {B B' : Sort uB} :
    (m : MapClass) →
    (pa : Param (mapArrowVariance m).1.1 (mapArrowVariance m).1.2 A A') →
    (pb : Param (mapArrowVariance m).2.1 (mapArrowVariance m).2.2 B B') →
    Map m (RArrow pa.R pb.R)
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := fun f a' => pb.cov.map (f (pa.contra.map a')) }
  | map2a, pa, pb => { map := fun f a' => pb.cov.map (f (pa.contra.map a')),
                       mapInR := arrowCovMapInR pa.contra.map pa.contra.rInMap pb.cov.map pb.cov.mapInR }
  | map2b, pa, pb => { map := fun f a' => pb.cov.map (f (pa.contra.map a')),
                       rInMap := arrowCovRInMap pa.contra.map pa.contra.mapInR pb.cov.map pb.cov.rInMap }
  | map3,  pa, pb => { map := fun f a' => pb.cov.map (f (pa.contra.map a')),
                       mapInR := arrowCovMapInR pa.contra.map pa.contra.rInMap pb.cov.map pb.cov.mapInR,
                       rInMap := arrowCovRInMap pa.contra.map pa.contra.mapInR pb.cov.map pb.cov.rInMap }
  | map4,  pa, pb => { map := fun f a' => pb.cov.map (f (pa.contra.map a')),
                       mapInR := arrowCovMapInR pa.contra.map pa.contra.rInMap pb.cov.map pb.cov.mapInR,
                       rInMap := arrowCovRInMap pa.contra.map pa.contra.mapInR pb.cov.map pb.cov.rInMap,
                       rInMapK := fun _ _ _ =>
                         RArrow.allEq (fun b b' => pb.cov.subsingleton b b') _ _ }

/-- the contravariant half `Map n (sym (RArrow RA RB))` from A's cov + B's contra (the mirror). -/
def arrowContra {A A' : Type u} {B B' : Sort uB} :
    (n : MapClass) →
    (pa : Param (mapArrowVariance n).1.2 (mapArrowVariance n).1.1 A A') →
    (pb : Param (mapArrowVariance n).2.2 (mapArrowVariance n).2.1 B B') →
    Map n (fun (f' : A' → B') (f : A → B) => RArrow pa.R pb.R f f')
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := fun f' a => pb.contra.map (f' (pa.cov.map a)) }
  | map2a, pa, pb => { map := fun f' a => pb.contra.map (f' (pa.cov.map a)),
                       mapInR := arrowContraMapInR pa.cov.map pa.cov.rInMap pb.contra.map pb.contra.mapInR }
  | map2b, pa, pb => { map := fun f' a => pb.contra.map (f' (pa.cov.map a)),
                       rInMap := arrowContraRInMap pa.cov.map pa.cov.mapInR pb.contra.map pb.contra.rInMap }
  | map3,  pa, pb => { map := fun f' a => pb.contra.map (f' (pa.cov.map a)),
                       mapInR := arrowContraMapInR pa.cov.map pa.cov.rInMap pb.contra.map pb.contra.mapInR,
                       rInMap := arrowContraRInMap pa.cov.map pa.cov.mapInR pb.contra.map pb.contra.rInMap }
  | map4,  pa, pb => { map := fun f' a => pb.contra.map (f' (pa.cov.map a)),
                       mapInR := arrowContraMapInR pa.cov.map pa.cov.rInMap pb.contra.map pb.contra.mapInR,
                       rInMap := arrowContraRInMap pa.cov.map pa.cov.mapInR pb.contra.map pb.contra.rInMap,
                       rInMapK := fun _ _ _ =>
                         RArrow.allEq (fun b b' => pb.contra.subsingleton b' b) _ _ }

/-- arrow at any output class `(m,n)`, incl. `(4,4)`, from parts at the `arrowVariance`-minimal classes.
    Each joined-class part is weakened to what its half consumes (`cases m <;> cases n <;> rfl`). -/
def paramArrow {A A' : Type u} {B B' : Sort uB} (m n : MapClass)
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
