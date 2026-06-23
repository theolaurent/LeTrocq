/- Layer 4 — the driver: Expr → constraints → solve → assembled witness, end to end. -/
import Lean
import Trocq
open Lean Lean.Meta Lean.Elab Lean.Elab.Command
namespace Trocq.Tests
open Trocq Trocq.Solver MapClass

def flagshipTy := ∀ A : Type, A → A

/- FRONT HALF: the Expr → constraint → solve inference reproduces the paper's minimal classes. -/
run_cmd Command.liftTermElabM do
  -- `Nat → Nat` at (0,1): the two occurrences get DIFFERENT minimal classes.
  let e1 ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let (_, sol1) ← runSolve demoAtoms e1 (map0, map1)
  if sol1 = #[(map0,map1),(map1,map0),(map0,map1)] then pure ()
  else throwError "front-half regressed (Nat→Nat): {repr sol1}"
  -- the flagship `∀ A : Type, A → A` at (0,1): vars [Π, Type, A, →, use, use].
  let e2 := (← getConstInfo ``flagshipTy).value!
  let (_, sol2) ← runSolve demoAtoms e2 (map0, map1)
  if sol2 = #[(map0,map1),(map2a,map0),(map1,map1),(map0,map1),(map1,map0),(map0,map1)] then pure ()
  else throwError "flagship inference regressed (∀A:Type,A→A): {repr sol2}"

/- BACK HALF: generate the witness for `Nat → Nat` at root (1,0), then hard-check it. -/
run_cmd Command.liftTermElabM do
  let e ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let (wit, _, _) ← transfer demoAtoms e (map1, map0)
  let ty ← instantiateMVars (← inferType wit)
  addDecl (.defnDecl { name := `Trocq.Tests.transferred, levelParams := [], type := ty, value := wit,
                       hints := .opaque, safety := .safe })

/- the generated witness is a real `Param (1,0) (Nat→Nat) (Unary→Unary)` whose forward map is
   native function transport — and it COMPUTES: -/
example : Trocq.Tests.transferred.cov.down.map Nat.succ Unary.z = Unary.s Unary.z := rfl
/-- info: 'Trocq.Tests.transferred' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms Trocq.Tests.transferred

end Trocq.Tests
