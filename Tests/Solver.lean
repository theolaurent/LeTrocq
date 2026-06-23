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

/- BACK HALF: generate the witness for `Nat → Nat` at root (1,0), then hard-check it.
   With the rewired driver this is built by the GRADED `paramArrow` at the per-node minimal class
   (`depArrow (1,0)` ⇒ domain at (0,1), codomain at (1,0)) — no build-(3,3)-then-weaken. -/
run_cmd Command.liftTermElabM do
  let e ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let (wit, _, _) ← transfer demoAtoms e (map1, map0)
  let ty ← instantiateMVars (← inferType wit)
  addDecl (.defnDecl { name := `Trocq.Tests.transferred, levelParams := [], type := ty, value := wit,
                       hints := .opaque, safety := .safe })

/- a NESTED arrow `Nat → Nat → Nat` at root (1,0): multi-level assembly, each node at its own class. -/
run_cmd Command.liftTermElabM do
  let e ← mkArrow (mkConst ``Nat) (← mkArrow (mkConst ``Nat) (mkConst ``Nat))
  let (wit, _, _) ← transfer demoAtoms e (map1, map0)
  let ty ← instantiateMVars (← inferType wit)
  addDecl (.defnDecl { name := `Trocq.Tests.transferred2, levelParams := [], type := ty, value := wit,
                       hints := .opaque, safety := .safe })

/- the generated witness is a real `Param (1,0) (Nat→Nat) (Unary→Unary)` whose forward map is
   native function transport — and it COMPUTES: -/
example : Trocq.Tests.transferred.cov.down.map Nat.succ Unary.z = Unary.s Unary.z := rfl
/-- info: 'Trocq.Tests.transferred' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms Trocq.Tests.transferred

/- the nested witness is a real `Param (1,0) (Nat→Nat→Nat) (Unary→Unary→Unary)` and computes: -/
example : Trocq.Tests.transferred2.cov.down.map (· + ·) Unary.z (Unary.s Unary.z) = Unary.s Unary.z := rfl
#check (Trocq.Tests.transferred2 : Param.{0,0} .map1 .map0 (Nat → Nat → Nat) (Unary → Unary → Unary))

/- FORALL + TYPE end-to-end: transfer the POLYMORPHIC `∀ A : Type, A → A` at (0,1) — the driver builds
   the universe domain (`paramTypeAt`), goes under the binder, and assembles the body `A → A` from the
   bound variable's relatedness witness. This is the paper's flagship, now *assembled*, not just inferred. -/
def flagshipTy2 := ∀ A : Type, A → A
run_cmd Command.liftTermElabM do
  let e := (← getConstInfo ``flagshipTy2).value!
  let (wit, _, _) ← transfer demoAtoms e (map0, map1)
  let ty ← instantiateMVars (← inferType wit)
  addDecl (.defnDecl { name := `Trocq.Tests.flagshipWit, levelParams := [], type := ty, value := wit,
                       hints := .opaque, safety := .safe })

/- the generated witness relates the polymorphic type to itself at class (0,1) (asserted via a
   proof term to avoid codegen, since the witness is noncomputable — it uses funext): -/
example : True := by
  have : Param.{1, 1} .map0 .map1 (∀ A : Type, A → A) (∀ A : Type, A → A) := Trocq.Tests.flagshipWit
  trivial
/-- info: 'Trocq.Tests.flagshipWit' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms Trocq.Tests.flagshipWit

end Trocq.Tests
