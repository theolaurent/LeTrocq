/- The class lattice and dependency tables (validated against the paper). The grading itself is no longer a
   constraint solver — it is `Transfer.assemble` pushing a demand top-down through these tables — so what is
   tested here is the pure table/lattice algebra those demands flow through. -/
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

/- The demand-driven grading (`Transfer.assemble`) pushes a demanded class through these tables directly, so its
   per-node classes are exactly what the tables return: e.g. an arrow at `(0,1)` splits into `depArrow (0,1) =
   ((1,0),(0,1))` (dom then cod), and the flagship `∀ A : Type, A → A` at `(0,1)` builds its domain `Type` at
   `depPi (0,1) = ((2a,0),(0,1))`. Those table facts are checked directly below; the end-to-end assembly (that the
   generated `Param` really lands at each class and computes) is exercised in `Tests/Solver.lean`. -/

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
