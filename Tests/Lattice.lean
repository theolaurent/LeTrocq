/- The class lattice, dependency tables, and the solver (validated against the paper). -/
import Lean
import LeTrocq.Lattice
open Lean Lean.Elab Lean.Elab.Command
namespace LeTrocq.Tests
open LeTrocq MapClass ParamClass

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
  -- (3) nested `A → (B → C)` at (0,1): both arrows split into (1,0)/(0,1).
  let r3 := solve 5 [(0,(map0,map1))] [.depArrow 0 1 2, .depArrow 2 3 4]
  if r3 = #[(map0,map1),(map1,map0),(map0,map1),(map1,map0),(map0,map1)] then pure ()
  else throwError "solver regressed (nested arrow): {repr r3}"
  -- (4) seeded at the TOP class: an arrow propagates (4,4) to both parts.
  let r4 := solve 3 [(0,(map4,map4))] [.depArrow 0 1 2]
  if r4 = #[(map4,map4),(map4,map4),(map4,map4)] then pure ()
  else throwError "solver regressed (top): {repr r4}"
  -- (5) a `gev` chain raises a shared variable to the join of its uses.
  let r5 := solve 3 [(1,(map1,map0)), (2,(map0,map2a))] [.gev 0 1, .gev 0 2]
  if r5[0]! = (map1, map2a) then pure ()
  else throwError "solver regressed (gev join): {repr r5}"

/- ===================== lattice laws (`MapClass`) ===================== -/
example : ∀ a : MapClass, MapClass.le a a = true := by intro a; cases a <;> rfl
example : ∀ a b c : MapClass, MapClass.le a b = true → MapClass.le b c = true → MapClass.le a c = true := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide
example : ∀ a b : MapClass, MapClass.le a b = true → MapClass.le b a = true → a = b := by
  intro a b; cases a <;> cases b <;> decide
example : ∀ a b : MapClass, MapClass.le a (MapClass.join a b) = true := by
  intro a b; cases a <;> cases b <;> decide
example : ∀ a b : MapClass, MapClass.le b (MapClass.join a b) = true := by
  intro a b; cases a <;> cases b <;> decide
example : ∀ a b : MapClass, MapClass.le (MapClass.meet a b) a = true := by
  intro a b; cases a <;> cases b <;> decide
example : ∀ a b : MapClass, MapClass.join a b = MapClass.join b a := by intro a b; cases a <;> cases b <;> decide
example : ∀ a : MapClass, MapClass.join a a = a := by intro a; cases a <;> rfl

/- ===================== `ParamClass` laws + the axiom boundary as a property ===================== -/
example : ∀ a : ParamClass, ParamClass.negate (ParamClass.negate a) = a := by intro ⟨x, y⟩; rfl
example : ∀ a : ParamClass, ParamClass.le ParamClass.bot a = true := by intro ⟨x, y⟩; cases x <;> cases y <;> decide
example : ∀ a : ParamClass, ParamClass.le a ParamClass.top = true := by intro ⟨x, y⟩; cases x <;> cases y <;> decide
/-- the axiom boundary is *exactly* `{0,1,2a}²`. -/
example : ∀ a : ParamClass,
    ParamClass.requiresAxiom a = false ↔ (MapClass.le a.1 map2a = true ∧ MapClass.le a.2 map2a = true) := by
  intro ⟨x, y⟩; cases x <;> cases y <;> decide

/- ===================== more dependency-table entries ===================== -/
example : depArrow (map4, map4) = ((map4,map4),(map4,map4)) := rfl
example : depPi    (map0, map1) = ((map2a,map0),(map0,map1)) := rfl
example : depPi    (map2a, map0) = ((map0,map4),(map2a,map0)) := rfl   -- Π domain needs the full equivalence
example : depType  (map0, map1)  = ParamClass.bot := rfl              -- no axiom ⇒ trivial sort relation
example : depType  (map0, map2b) = ParamClass.top := rfl              -- 2b ⇒ univalence ⇒ top

end LeTrocq.Tests
