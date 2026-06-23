/- Layer 1 — the class lattice, dependency tables, and the solver (validated against the paper). -/
import Lean
import Trocq.Lattice
open Lean Lean.Elab Lean.Elab.Command
namespace Trocq.Tests
open Trocq MapClass ParamClass

/- lattice: 2a and 2b are incomparable; join = 3, meet = 1 -/
example : MapClass.join map2a map2b = map3 := rfl
example : MapClass.meet map2a map2b = map1 := rfl
example : MapClass.le map2a map2b = false := rfl
example : MapClass.le map2b map2a = false := rfl

/- the axiom boundary {0,1,2a}² -/
example : ParamClass.requiresAxiom (map2a, map2a) = false := rfl
example : ParamClass.requiresAxiom (map0, map2b) = true  := rfl
example : ParamClass.requiresAxiom (map3, map0)  = true  := rfl

/- dependency tables (paper Fig. dep-pi), via the symmetry-combining formula -/
example : depPi    (map1, map0) = ((map0,map2a),(map1,map0)) := rfl
example : depArrow (map1, map0) = ((map0,map1), (map1,map0)) := rfl
example : depArrow (map0, map1) = ((map1,map0), (map0,map1)) := rfl   -- symmetric
example : depPi    (map4, map0) = ((map0,map4), (map4,map0)) := rfl

/- the SOLVER (run compiled, asserted by hand — `solve`'s for-loop doesn't reduce by `rfl`). -/
run_cmd Command.liftTermElabM do
  -- (1) `A → B` at (0,1): dom→(1,0), cod→(0,1).
  let r1 := solve 3 [(0, (map0,map1))] [.depArrow 0 1 2]
  if r1 = #[(map0,map1),(map1,map0),(map0,map1)] then pure ()
  else throwError "solver regressed (A→B @ (0,1)): {repr r1}"
  -- (2) the flagship `∀ A : Type, A → A` at (0,1): domain Type→(2a,0), bound A→(1,1).
  let cs : List Cstr := [.depPi 0 1 2, .depType 1 3, .depArrow 2 4 5, .gev 3 4, .gev 3 5]
  let r2 := solve 6 [(0, (map0,map1))] cs
  if r2 = #[(map0,map1),(map2a,map0),(map0,map1),(map1,map1),(map1,map0),(map0,map1)] then pure ()
  else throwError "solver regressed (∀A:Type,A→A @ (0,1)): {repr r2}"

end Trocq.Tests
