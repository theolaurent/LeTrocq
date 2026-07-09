/-
The lattice algebra: the MapClass/ParamClass diamond, its order/join/meet, and the axiom boundary.

The computational spine of the graded system (the port of Trocq's `elpi/class.elpi`). Pure, finite, no
proofs/metaprogramming — validated with `rfl`/`#eval` in the tests. The per-former GRADING tables
(`arrowVariance`/`forallVariance`) now live with their combinators in `Combinators/`; `Transfer.assemble`
pushes a demanded class top-down through them. The proof-heavy combinators (`Combinators/`)
and the driver (`Driver/`) build on top of this.
-/
namespace LeTrocq

/- ===================== map-class lattice  (0 < 1 < {2a,2b} < 3 < 4) ===================== -/
inductive MapClass | map0 | map1 | map2a | map2b | map3 | map4
deriving DecidableEq, Repr, Inhabited

namespace MapClass

/-- partial order `a ≤ b` on the diamond. -/
def le (a b: MapClass) : Bool :=
  match a, b with
  | map0, _ => true
  | _, map0 => false
  | map1, _ => true
  | _, map1 => false
  | map2a, map2b => false
  | map2b, map2a => false
  | map2a, _ => true
  | _, map2a => false
  | map2b, _ => true
  | _, map2b => false
  | map3, _ => true
  | _, map3 => false
  | map4, map4 => true

/-- least upper bound (join). -/
def join (a b : MapClass) : MapClass :=
  match a, b with
  | map0, x | x, map0 => x
  | map1, x | x, map1 => x
  | map2a, map2b | map2b, map2a => map3
  | map2a, x | x, map2a => x
  | map2b, x | x, map2b => x
  | map3, x | x, map3 => x
  | map4, map4 => map4

/-- greatest lower bound (meet). -/
def meet (a b : MapClass) : MapClass :=
  match a, b with
  | map0, _ | _, map0 => map0
  | map1, _ | _, map1 => map1
  | map2a, map2b | map2b, map2a => map1
  | map2a, _ | _, map2a => map2a
  | map2b, _ | _, map2b => map2b
  | map3, _ | _, map3 => map3
  | map4, map4 => map4

end MapClass

/- ===================== parametricity classes (pairs) ===================== -/
abbrev ParamClass := MapClass × MapClass

namespace ParamClass
open MapClass
def le (a b : ParamClass) : Bool := MapClass.le a.1 b.1 && MapClass.le a.2 b.2
def join (a b : ParamClass) : ParamClass := (MapClass.join a.1 b.1, MapClass.join a.2 b.2)
/-- swap the two transport directions (relation symmetry). -/
def negate (a : ParamClass) : ParamClass := (a.2, a.1)
/-- invert an output demand `c` through a per-direction primitive table `f` (output class ↦ minimal part
    class) to the minimal part class: the cov requirement joined with the negated contra one. The shared spine
    of every former's `…Variance` (`listVariance`/`eqVariance`/…); the pair-valued formers (`arrow`/`forall`/
    `sigma`) apply it componentwise inline. -/
def variance (f : MapClass → ParamClass) (c : ParamClass) : ParamClass :=
  join (f c.1) (negate (f c.2))
def bot : ParamClass := (map0, map0)
def top : ParamClass := (map4, map4)
/-- needs an axiom (univalence on a sort / funext on Π) iff some component is ≥ 2b. -/
def requiresAxiom (a : ParamClass) : Bool := !MapClass.le a.1 map2a || !MapClass.le a.2 map2a
end ParamClass

/- The per-former GRADING tables (`arrowVariance`/`forallVariance`: output class → minimal part classes)
   now live with their combinators in `Combinators/Arrow.lean` and `Combinators/Forall.lean`. -/

end LeTrocq
