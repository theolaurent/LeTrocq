/- The class lattice: the MapClass/ParamClass diamond, its order/join/meet, and the axiom boundary. (The
   per-former grading tables `arrowVariance`/`forallVariance` moved to `ParamCC/`; they are tested next to their
   combinators in `Tests/ParamCC/Arrow.lean` and `Tests/ParamCC/Forall.lean`.) -/
import LeTrocq.Lattice
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

end LeTrocq.Tests
