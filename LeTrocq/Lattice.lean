/-
The lattice algebra + dependency tables.

The computational spine of the graded system (the port of Trocq's `elpi/class.elpi`). Pure, finite,
no proofs/metaprogramming — validated against the paper's tables with `rfl`/`#eval` below. The
grading itself is no longer a constraint solver: `Transfer.assemble` pushes a demanded class top-down
through the `depArrow`/`depPi`/`depType` tables here (bidir_solver.md). The proof-heavy combinators
(`ParamCC`) and the driver (`Transfer`) build on top of this.
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
def meet (a b : ParamClass) : ParamClass := (MapClass.meet a.1 b.1, MapClass.meet a.2 b.2)
/-- swap the two transport directions (relation symmetry). -/
def negate (a : ParamClass) : ParamClass := (a.2, a.1)
def bot : ParamClass := (map0, map0)
def top : ParamClass := (map4, map4)
/-- needs an axiom (univalence on a sort / funext on Π) iff some component is ≥ 2b. -/
def requiresAxiom (a : ParamClass) : Bool := !MapClass.le a.1 map2a || !MapClass.le a.2 map2a
end ParamClass

/- ===================== dependency tables (verbatim from class.elpi) ===================== -/
open MapClass ParamClass in
/-- per-map-class minimal (domain, codomain) classes for a dependent Π. -/
def mapDepPi : MapClass → (ParamClass × ParamClass)
  | map0  => ((map0,map0), (map0,map0))
  | map1  => ((map0,map2a),(map1,map0))
  | map2a => ((map0,map4), (map2a,map0))
  | map2b => ((map0,map2a),(map2b,map0))
  | map3  => ((map0,map4), (map3,map0))
  | map4  => ((map0,map4), (map4,map0))

open MapClass ParamClass in
/-- per-map-class minimal (domain, codomain) classes for a non-dependent arrow. -/
def mapDepArrow : MapClass → (ParamClass × ParamClass)
  | map0  => ((map0,map0), (map0,map0))
  | map1  => ((map0,map1), (map1,map0))
  | map2a => ((map0,map2b),(map2a,map0))
  | map2b => ((map0,map2a),(map2b,map0))
  | map3  => ((map0,map3), (map3,map0))
  | map4  => ((map0,map4), (map4,map0))

/-- minimal (domain-class, codomain-class) to translate a Π at output class `c`. -/
def depPi (c : ParamClass) : ParamClass × ParamClass :=
  let (am, bm) := mapDepPi c.1
  let (an, bn) := mapDepPi c.2
  (ParamClass.join am (ParamClass.negate an), ParamClass.join bm (ParamClass.negate bn))

/-- minimal (domain-class, codomain-class) to translate an arrow at output class `c`. -/
def depArrow (c : ParamClass) : ParamClass × ParamClass :=
  let (am, bm) := mapDepArrow c.1
  let (an, bn) := mapDepArrow c.2
  (ParamClass.join am (ParamClass.negate an), ParamClass.join bm (ParamClass.negate bn))

/-- the relation-field lower bound for a sort at output class `c` (axiom boundary): the universe
    combinator needs an equivalence-strength relation exactly when the output needs an axiom. -/
def depType (c : ParamClass) : ParamClass :=
  if ParamClass.requiresAxiom c then ParamClass.top else ParamClass.bot

end LeTrocq
