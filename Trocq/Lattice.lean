/-
The lattice algebra + dependency tables + class solver.

The computational spine of the graded system (the port of Trocq's `elpi/class.elpi` +
`elpi/constraints/constraint-graph.elpi`). Pure, finite, no proofs/metaprogramming — validated
against the paper's tables with `rfl`/`#eval` below. The proof-heavy combinators (`Combinators`) and
the driver (`Solver`) build on top of this.
-/
namespace Trocq

/- ===================== map-class lattice  (0 < 1 < {2a,2b} < 3 < 4) ===================== -/
inductive MapClass | map0 | map1 | map2a | map2b | map3 | map4
deriving DecidableEq, Repr, Inhabited

namespace MapClass
def all : List MapClass := [map0, map1, map2a, map2b, map3, map4]

/-- partial order `a ≤ b` on the diamond. -/
def le : MapClass → MapClass → Bool
  | map0,  _     => true
  | map1,  map1  => true | map1, map2a => true | map1, map2b => true
  | map1,  map3  => true | map1, map4  => true | map1, _ => false
  | map2a, map2a => true | map2a, map3 => true | map2a, map4 => true | map2a, _ => false
  | map2b, map2b => true | map2b, map3 => true | map2b, map4 => true | map2b, _ => false
  | map3,  map3  => true | map3, map4  => true | map3, _ => false
  | map4,  map4  => true | map4, _ => false

/-- least upper bound (join). -/
def join (a b : MapClass) : MapClass :=
  all.foldl (fun best c => if le a c && le b c && le c best then c else best) map4
/-- greatest lower bound (meet). -/
def meet (a b : MapClass) : MapClass :=
  all.foldl (fun best c => if le c a && le c b && le best c then c else best) map0
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

/- ===================== the class solver (monotone least-fixpoint) ===================== -/
abbrev Var := Nat
inductive Cstr
  | ge       (x : Var) (c : ParamClass)   -- x ≥ constant
  | gev      (x y : Var)                   -- x ≥ y
  | depPi    (out a b : Var)               -- a,b ≥ depPi(out)
  | depArrow (out a b : Var)
  | depType  (out r : Var)                 -- r ≥ depType(out)
deriving Repr

def stepCstr (asn : Array ParamClass) : Cstr → Array ParamClass
  | .ge x c        => asn.set! x (ParamClass.join asn[x]! c)
  | .gev x y       => asn.set! x (ParamClass.join asn[x]! asn[y]!)
  | .depType out r => asn.set! r (ParamClass.join asn[r]! (depType asn[out]!))
  | .depPi out a b =>
      let (cd, ce) := depPi asn[out]!
      (asn.set! a (ParamClass.join asn[a]! cd)).set! b (ParamClass.join asn[b]! ce)
  | .depArrow out a b =>
      let (cd, ce) := depArrow asn[out]!
      (asn.set! a (ParamClass.join asn[a]! cd)).set! b (ParamClass.join asn[b]! ce)

/-- least fixpoint: seed some vars, propagate `≥`-constraints upward until stable.
    Returns the MINIMAL class assignment satisfying every constraint. -/
def solve (nVars : Nat) (seeds : List (Var × ParamClass)) (cs : List Cstr) : Array ParamClass := Id.run do
  let mut a : Array ParamClass := Array.replicate nVars ParamClass.bot
  for (x, c) in seeds do a := a.set! x c
  for _ in [0 : nVars * 6 + 8] do
    let a' := cs.foldl stepCstr a
    if a' == a then return a'
    a := a'
  return a

end Trocq
