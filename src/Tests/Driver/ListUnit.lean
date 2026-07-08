/-
Tests for the GROUND base `List Unit ≃ Nat` and its GROUND TERMS (`Examples.ListUnit`).

Covers: the type surface (`transfer`/`trocq` treat `List Unit` as an opaque atom ≃ `Nat`, beating the `List`
relator and the diagonal); leaf-by-leaf translation of PLAIN list constructors via the partial-application
patterns `@List.cons Unit () ↦ Nat.succ` / `@List.nil Unit ↦ Nat.zero`; and the axiom footprint. The bulk of
the `example … := rfl` facts live in `Examples.ListUnit` and fire on import.
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

/- ===================== plain list constructors translate leaf-by-leaf via the ground-term patterns ===================== -/
example : (translate (List.cons () (List.cons () (List.cons () (@List.nil Unit))))) = 3 := rfl
example : RLUN (List.cons () (@List.nil Unit)) 1 := relate (List.cons () (@List.nil Unit))
-- built from `[…]` notation (same underlying `List.cons`/`List.nil`).
example : (translate ([(), ()] : List Unit)) = 2 := rfl
example : RLUN [(), (), ()] 3 := relate ([(), (), ()] : List Unit)

/- ===================== axiom footprint ===================== -/
/-- info: 'LeTrocq.Examples.RLU' depends on axioms: [propext] -/
#guard_msgs in #print axioms RLU
