/-
Tests for the GROUND (non-atomic closed) base `List Unit ≃ Nat` (`Examples.ListUnit`).

Covers: the type surface (`transfer`/`trocq` treat `List Unit` as an opaque atom ≃ `Nat`, beating the `List`
relator and the diagonal), transport-via-map of raw lists, leaf-by-leaf term translation via the registered
`lzero`/`lsucc` primitives, and the axiom footprint (the ground base + a generated witness stay choice-free).
The bulk of the computational `example … := rfl` facts live in `Examples.ListUnit` and fire on import.
-/
import Examples.ListUnit
open LeTrocq LeTrocq.Examples MapClass

/- ===================== the ground base resolves whole (not via the `List` relator / diagonal) ===================== -/
example : (transfer from (List Unit)).cov.map [(), (), ()] = 3 := rfl
example : (transfer from (List Unit)).contra.map 0 = ([] : List Unit) := rfl
-- CHECK mode with an explicit target.
example : (transfer from (List Unit) to Nat).cov.map [()] = 1 := rfl
-- nested inside a relator argument.
example : (transfer from (List Unit → Bool)).cov.map (fun l => l.length == 0) 0 = true := rfl

/- ===================== leaf-by-leaf term translation ===================== -/
example : (translate (lsucc (lsucc (lsucc lzero)))) = 3 := rfl
example : RLUN (lsucc (lsucc (lsucc lzero))) 3 := relate (lsucc (lsucc (lsucc lzero)))

/- ===================== axiom footprint ===================== -/
/-- info: 'LeTrocq.Examples.RLU' depends on axioms: [propext] -/
#guard_msgs in #print axioms RLU

/-- info: 'LeTrocq.Examples.LSuccR' does not depend on any axioms -/
#guard_msgs in #print axioms LSuccR
