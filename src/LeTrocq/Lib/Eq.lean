/-
The LeTrocq STANDARD LIBRARY: `Eq` (propositional equality).

`a = b` relates to `a' = b'` when the two sides are related pointwise and the underlying type carries enough
of the correspondence to transport the equality. Because `a = b` / `a' = b'` are PROPOSITIONS, the carried
relation is trivial (`PLift True`) and the witness carries no data above class 1 — so, like every other
relator, `Eq` is GRADED: to transport the equality in one direction it needs only the underlying type's
COMPLETENESS (`rInMap`, class 2b) in that direction, never a full equivalence. The maximum demand is `(2b,2b)`
(both directions); a one-directional transport — e.g. the `trocq` goal seed `(0,1)` — needs only `(0,2b)`.
(Contrast `List`/`Prod`, whose element needs only the bare relation: `Eq` transports an equation, so it needs
the maps' completeness, but still stops short of a bijection.)

(Monomorphic at `Type`; a `Sort`-polymorphic `Eq` witness is future work.)
-/
import LeTrocq.Driver.Registry
import LeTrocq.Combinators.Universe
namespace LeTrocq.Lib
open LeTrocq MapClass

/-- forward transport `a = b → a' = b'`, from the underlying type's COVARIANT completeness (`rInMap`, class
    2b): each endpoint's relatedness pins `map · = ·`, so the source equality carries over. Half of the old
    `eqCorr`, split out so the covariant arm can consume it without the contravariant direction. -/
theorem eqFwd {A A' : Type} {R : A → A' → Type} (cov : Map2bHas R)
    {a b : A} {a' b' : A'} (aRel : R a a') (bRel : R b b') : a = b → a' = b' :=
  fun h => by rw [← cov.rInMap a a' aRel, ← cov.rInMap b b' bRel, h]

/-- backward transport `a' = b' → a = b`, the mirror, from the type's CONTRAVARIANT completeness. -/
theorem eqBwd {A A' : Type} {R : A → A' → Type} (contra : Map2bHas (fun (b : A') (a : A) => R a b))
    {a b : A} {a' b' : A'} (aRel : R a a') (bRel : R b b') : a' = b' → a = b :=
  fun h => by rw [← contra.rInMap a' a aRel, ← contra.rInMap b' b bRel, h]

/- ===================== the GRADING table (a `Prop` output caps each direction at 2b) ===================== -/
/-- per-map-class minimal underlying-type class for `Eq`: the transport map needs only completeness (`rInMap`,
    2b) in its own direction, and — the objects being propositions — nothing above the map. Parallel to
    `mapListVariance`, but capped at 2b (`Eq` never needs its type argument at 3/4). -/
def mapEqVariance : MapClass → ParamClass
  | map0 => (map0,  map0)
  | _    => (map2b, map0)

/-- minimal underlying-type class to build `Eq` at output class `c`: the cov requirement joined with the
    negated contra one. Tops out at `(2b,2b)`; a one-directional demand (e.g. `(0,1)`) needs only `(0,2b)`. -/
def eqVariance (c : ParamClass) : ParamClass := ParamClass.variance mapEqVariance c

/-- the covariant half from the underlying type at `mapEqVariance m`: empty below class 1, the forward
    transport `eqFwd` at class ≥ 1 (every higher `Prop` field is free via `propMapHas`). The carried relation
    is the trivial `PLift True` — a proposition transports no data. -/
def eqCov {A A' : Type} {a b : A} {a' b' : A'} :
    (m : MapClass) →
    (pa : Param (mapEqVariance m).1 (mapEqVariance m).2 A A') →
    pa.R a a' → pa.R b b' → MapHas m (fun (_ : a = b) (_ : a' = b') => PLift True)
  | map0,  _,  _,    _    => {}
  | map1,  pa, aRel, bRel => propMapHas (eqFwd pa.cov aRel bRel) map1
  | map2a, pa, aRel, bRel => propMapHas (eqFwd pa.cov aRel bRel) map2a
  | map2b, pa, aRel, bRel => propMapHas (eqFwd pa.cov aRel bRel) map2b
  | map3,  pa, aRel, bRel => propMapHas (eqFwd pa.cov aRel bRel) map3
  | map4,  pa, aRel, bRel => propMapHas (eqFwd pa.cov aRel bRel) map4

/-- the contravariant half from the type's contra at `mapEqVariance n` — the mirror (backward transport). -/
def eqContra {A A' : Type} {a b : A} {a' b' : A'} :
    (n : MapClass) →
    (pa : Param (mapEqVariance n).2 (mapEqVariance n).1 A A') →
    pa.R a a' → pa.R b b' → MapHas n (fun (_ : a' = b') (_ : a = b) => PLift True)
  | map0,  _,  _,    _    => {}
  | map1,  pa, aRel, bRel => propMapHas (eqBwd pa.contra aRel bRel) map1
  | map2a, pa, aRel, bRel => propMapHas (eqBwd pa.contra aRel bRel) map2a
  | map2b, pa, aRel, bRel => propMapHas (eqBwd pa.contra aRel bRel) map2b
  | map3,  pa, aRel, bRel => propMapHas (eqBwd pa.contra aRel bRel) map3
  | map4,  pa, aRel, bRel => propMapHas (eqBwd pa.contra aRel bRel) map4

/-- `a = b ≃ a' = b'` at ANY output class `(m,n)`, from the underlying type at the `eqVariance`-minimal class
    and the two endpoints related. A RELATOR keyed by `Eq`: the first triple is the TYPE argument, the next
    two are the term (endpoint) arguments. The single type witness is weakened to what each half consumes;
    every obligation is `join ≥ component`, discharged by `cases m <;> cases n <;> rfl`. -/
@[trocq] def paramEq (m n : MapClass) (A A' : Type)
    (pa : Param (eqVariance (m, n)).1 (eqVariance (m, n)).2 A A')
    (a : A) (a' : A') (aRel : pa.R a a') (b : A) (b' : A') (bRel : pa.R b b') :
    Param m n (a = b) (a' = b') where
  R := fun _ _ => PLift True
  cov := eqCov m (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) aRel bRel
  contra := eqContra n (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl)) aRel bRel

end LeTrocq.Lib
