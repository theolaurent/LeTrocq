/-
MILESTONE 6, layer 3: the map/comap-carrying COMBINATORS (the proof-heavy heart).

Layers 1–2 gave the class algebra and the weakening maps. Here we give the constructions that
*build* a `Param` for a composite type former (`→`, `Type`) out of `Param`s for its parts, at a class
governed by the Layer-1 dependency tables. Three things to demonstrate, each a load-bearing point of
the whole Trocq story:

  • `paramArrow33` — the arrow combinator at class (3,3): full soundness+completeness BOTH directions.
    Completeness (`R_in_map`) needs **funext** — a *theorem* in Lean, so this is axiom-free. (The
    coherence field `R_in_mapK` that lifts 3→4 is the adjoint-equivalence triangle; Trocq's `Param44`
    proves it with the half-adjoint machinery — deferred here, exactly the (3 vs 4) gap the design names.)

  • `paramArrowLow` — the SAME former at the minimal class (0,1): just a backward map, ZERO proofs.
    This is why the lattice earns its keep — staying low is staying cheap.

  • `paramType` — the universe combinator at (2a,2a): the **no-univalence ceiling**. `map_in_R`
    (`A = A' → Param A A'`) is free (it's `Eq.rec`); `R_in_map` (`Param A A' → A = A'`) would need
    univalence, so `Type` is BLOCKED above 2a — precisely what Layer 1's `depType`/`requiresAxiom` encodes.

Built on the Layer-2 file's hierarchy + weakening.
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

/- ===================== arrow combinator at (3,3) — funext, axiom-free ===================== -/
section Arrow33
variable {A B A' B' : Type u} {RA : A → A' → Type v} {RB : B → B' → Type v}

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

end Arrow33

/- ===================== arrow combinator at the MINIMAL class (0,1) — ZERO proofs ===================== -/
section ArrowLow
variable {A B A' B' : Type u} {RA : A → A' → Type v} {RB : B → B' → Type v}

/-- arrow at (0,1): the codomain is only used contravariantly, the domain only covariantly, so all we
    can (and need to) produce is the backward map `(A'→B') → (A→B)`. No `map_in_R`/`R_in_map`/funext.
    `mapDepArrow map1 = ((map0,map1),(map1,map0))`: domain needs cov≥1, codomain needs contra≥1. -/
def paramArrowLow (pa : Param.{u,v} map1 map0 A A') (pb : Param.{u,v} map0 map1 B B') :
    Param.{u, max u v} map0 map1 (A → B) (A' → B') where
  R := RArrow pa.R pb.R
  cov := ULift.up {}
  contra := ULift.up { map := fun f' a => pb.contra.down.map (f' (pa.cov.down.map a)) }

end ArrowLow

/- ===================== the universe combinator — the no-univalence ceiling (2a,2a) ===================== -/
/-- a reflexive `Param` at (1,1): the identity, with `R a b := PLift (a = b)`. -/
def paramId (A : Type 0) : Param.{0,0} map1 map1 A A where
  R := fun a b => PLift (a = b)
  cov := ULift.up { map := id }
  contra := ULift.up { map := id }

/-- the universe combinator at (2a,2a). The relation on types IS `Param 1 1`. Forward map = `id`;
    `map_in_R : A = A' → Param A A'` is `Eq.rec` of `paramId` — **no univalence**. The completeness
    field `R_in_map : Param A A' → A = A'` is what would need univalence, so we stop at 2a: this is the
    `Type`-universe ceiling that Layer 1's `requiresAxiom`/`depType` enforces. -/
def paramType : Param.{1,1} map2a map2a (Type 0) (Type 0) where
  R := fun A A' => Param.{0,0} map1 map1 A A'
  cov :=
    { map := id
      map_in_R := fun A A' h => by subst h; exact paramId A }
  contra :=
    { map := id
      map_in_R := fun A' A h => by subst h; exact paramId A' }

/- ===================== assembled witnesses over `Nat ≃ Unary` (used by tests + the driver) ===================== -/
-- the arrow witness `Nat→Nat ~ Unary→Unary` at (3,3), built by weakening RN (4,4) into the parts:
def RN33 : Param.{0,0} map3 map3 Nat Unary := RN.weaken (sm := map4) (sn := map4) rfl rfl
def arrowNU : Param.{0,0} map3 map3 (Nat → Nat) (Unary → Unary) := paramArrow33 RN33 RN33

-- weakened to (1,0): "just the transported function".
def arrowNU_fun : Param.{0,0} map1 map0 (Nat → Nat) (Unary → Unary) :=
  arrowNU.weaken (sm := map3) (sn := map3) rfl rfl

-- the minimal-class arrow, built from the cheap (1,0)/(0,1) splits of RN.
def RN10 : Param.{0,0} map1 map0 Nat Unary := RN.weaken (sm := map4) (sn := map4) rfl rfl
def RN01 : Param.{0,0} map0 map1 Nat Unary := RN.weaken (sm := map4) (sn := map4) rfl rfl
def arrowNU_low : Param.{0,0} map0 map1 (Nat → Nat) (Unary → Unary) := paramArrowLow RN10 RN01

end Trocq
