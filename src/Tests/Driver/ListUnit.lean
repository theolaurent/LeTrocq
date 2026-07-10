/-
The ground base `List Unit ≃ Nat` and its ground terms (`Examples.ListUnit`). Covers the type surface
(`List Unit` resolves as an opaque atom, beating the `List` relator and the diagonal), leaf-by-leaf
translation of plain list constructors, and the axiom footprint.
-/
import Examples.ListUnit
open LeTrocq LeTrocq.Examples MapClass

/- ===================== the ground base resolves whole (not via the `List` relator / diagonal) ===================== -/
example : (transfer from (List Unit)).cov.map [(), (), ()] = 3 := rfl
example : (transfer from (List Unit)).contra.map 0 = ([] : List Unit) := rfl
-- explicit target.
example : (transfer from (List Unit) to Nat).cov.map [()] = 1 := rfl
-- nested inside a relator argument.
example : (transfer from (List Unit → Bool)).cov.map (fun l => l.length == 0) 0 = true := rfl

/- ===================== plain list constructors translate leaf-by-leaf ===================== -/
example : (translate (List.cons () (List.cons () (List.cons () (@List.nil Unit))))) = 3 := rfl
example : RLUN (List.cons () (@List.nil Unit)) 1 := relate (List.cons () (@List.nil Unit))
-- from `[…]` notation (same underlying constructors).
example : (translate ([(), ()] : List Unit)) = 2 := rfl
example : RLUN [(), (), ()] 3 := relate ([(), (), ()] : List Unit)

/- ===================== BACKWARD ground terms: `Nat ⤳ List Unit` =====================
   The reverse of `@List.cons Unit () ↦ Nat.succ` / `@List.nil Unit ↦ Nat.zero`. A ground term has a fixed
   prefix (here the type arg `Unit` + value `()`), just like a typeclass operation `@HAdd.hAdd _ _ _ inst`,
   so it can only be filed as a ground term — and its reverse is what a `trocq` goal over the B-side type
   needs. `translate` exercises the reverse counterpart; `relate` exercises the `symPrimitive`d witness. -/
example : (translate (Nat.succ (Nat.succ Nat.zero)) : List Unit) = [(), ()] := rfl
example : (translate (Nat.zero : Nat)) = ([] : List Unit) := rfl
example : RLUN [()] 1 := relate (Nat.succ Nat.zero)

/- ===================== axiom footprint ===================== -/
/-- info: 'LeTrocq.Examples.RLU' depends on axioms: [propext] -/
#guard_msgs in #print axioms RLU
