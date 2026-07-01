/- The driver: Expr → constraints → solve → assembled witness, end to end. -/
import Lean
import LeTrocq
import Examples.NatUnary
open Lean Lean.Meta Lean.Elab Lean.Elab.Command
namespace LeTrocq.Tests
open LeTrocq LeTrocq.Solver LeTrocq.Transfer MapClass LeTrocq.Examples

def flagshipTy := ∀ A : Type, A → A

/- FRONT HALF: the Expr → constraint → solve inference reproduces the paper's minimal classes. -/
run_cmd Command.liftTermElabM do
  -- `Nat → Nat` at (0,1): the two occurrences get DIFFERENT minimal classes.
  let e1 ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let (_, sol1) ← runSolve e1 (map0, map1)
  if sol1 = #[(map0,map1),(map1,map0),(map0,map1)] then pure ()
  else throwError "front-half regressed (Nat→Nat): {repr sol1}"
  -- the flagship `∀ A : Type, A → A` at (0,1): vars [Π, Type, A, →, use, use].
  let e2 := (← getConstInfo ``flagshipTy).value!
  let (_, sol2) ← runSolve e2 (map0, map1)
  if sol2 = #[(map0,map1),(map2a,map0),(map1,map1),(map0,map1),(map1,map0),(map0,map1)] then pure ()
  else throwError "flagship inference regressed (∀A:Type,A→A): {repr sol2}"

/- BACK HALF: generate the witness for `Nat → Nat` at root (1,0), then hard-check it.
   With the rewired driver this is built by the GRADED `paramArrow` at the per-node minimal class
   (`depArrow (1,0)` ⇒ domain at (0,1), codomain at (1,0)) — no build-(3,3)-then-weaken. -/
run_cmd Command.liftTermElabM do
  let e ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let wit ← transfer e (map1, map0)
  let ty ← instantiateMVars (← inferType wit)
  addDecl (.defnDecl { name := `LeTrocq.Tests.transferred, levelParams := [], type := ty, value := wit,
                       hints := .opaque, safety := .safe })

/- a NESTED arrow `Nat → Nat → Nat` at root (1,0): multi-level assembly, each node at its own class. -/
run_cmd Command.liftTermElabM do
  let e ← mkArrow (mkConst ``Nat) (← mkArrow (mkConst ``Nat) (mkConst ``Nat))
  let wit ← transfer e (map1, map0)
  let ty ← instantiateMVars (← inferType wit)
  addDecl (.defnDecl { name := `LeTrocq.Tests.transferred2, levelParams := [], type := ty, value := wit,
                       hints := .opaque, safety := .safe })

/- the generated witness is a real `Param (1,0) (Nat→Nat) (Unary→Unary)` whose forward map is
   native function transport — and it COMPUTES: -/
example : LeTrocq.Tests.transferred.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl
/-- info: 'LeTrocq.Tests.transferred' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms LeTrocq.Tests.transferred

/- the nested witness is a real `Param (1,0) (Nat→Nat→Nat) (Unary→Unary→Unary)` and computes: -/
example : LeTrocq.Tests.transferred2.cov.map (· + ·) Unary.z (Unary.s Unary.z) = Unary.s Unary.z := rfl
example : True := by
  have : Param .map1 .map0 (Nat → Nat → Nat) (Unary → Unary → Unary) := LeTrocq.Tests.transferred2
  trivial

/- FORALL + TYPE end-to-end: transfer the POLYMORPHIC `∀ A : Type, A → A` at (0,1) — the driver builds
   the universe domain (`paramTypeAt`), goes under the binder, and assembles the body `A → A` from the
   bound variable's relatedness witness. This is the paper's flagship, now *assembled*, not just inferred. -/
def flagshipTy2 := ∀ A : Type, A → A
run_cmd Command.liftTermElabM do
  let e := (← getConstInfo ``flagshipTy2).value!
  let wit ← transfer e (map0, map1)
  let ty ← instantiateMVars (← inferType wit)
  addDecl (.defnDecl { name := `LeTrocq.Tests.flagshipWit, levelParams := [], type := ty, value := wit,
                       hints := .opaque, safety := .safe })

/- the generated witness relates the polymorphic type to itself at class (0,1) (asserted via a
   proof term to avoid codegen, since the witness is noncomputable — it uses funext): -/
example : True := by
  have : Param .map0 .map1 (∀ A : Type, A → A) (∀ A : Type, A → A) := LeTrocq.Tests.flagshipWit
  trivial
/-- info: 'LeTrocq.Tests.flagshipWit' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms LeTrocq.Tests.flagshipWit

/- MAP_TYPE: the same `∀ A : Type, A → A` at root (2b,0) forces the bound variable `A` to class
   (2b,2a) — ABOVE the old fixed (1,1) ceiling. The universe combinator now carries that inner class
   (`paramTypeAtInner`), so it assembles; under the old (1,1)-only `paramType` this would have failed. -/
run_cmd Command.liftTermElabM do
  let e := (← getConstInfo ``flagshipTy2).value!
  let wit ← transfer e (map2b, map0)
  let ty ← instantiateMVars (← inferType wit)
  addDecl (.defnDecl { name := `LeTrocq.Tests.flagshipWit2b, levelParams := [], type := ty, value := wit,
                       hints := .opaque, safety := .safe })
example : True := by
  have : Param .map2b .map0 (∀ A : Type, A → A) (∀ A : Type, A → A) := LeTrocq.Tests.flagshipWit2b
  trivial

/- (4,4) end-to-end: `Nat → Nat` transferred at the TOP class — now possible since the arrow propagates
   the full equivalence (the `(4,4)` coherence `R_in_mapK` holds by subsingleton). -/
run_cmd Command.liftTermElabM do
  let e ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let wit ← transfer e (map4, map4)
  let ty ← instantiateMVars (← inferType wit)
  addDecl (.defnDecl { name := `LeTrocq.Tests.transferred44, levelParams := [], type := ty, value := wit,
                       hints := .opaque, safety := .safe })
example : LeTrocq.Tests.transferred44.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl
example : True := by
  have : Param .map4 .map4 (Nat → Nat) (Unary → Unary) := LeTrocq.Tests.transferred44
  trivial

/- `Nat → Nat` transferred at several intermediate root classes — each generated witness computes. -/
run_cmd Command.liftTermElabM do
  let e ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let w3 ← transfer e (map3, map3)
  addDecl (.defnDecl { name := `LeTrocq.Tests.tr33, levelParams := [],
                       type := ← instantiateMVars (← inferType w3), value := ← instantiateMVars w3,
                       hints := .opaque, safety := .safe })
  let w2a ← transfer e (map2a, map0)
  addDecl (.defnDecl { name := `LeTrocq.Tests.tr2a, levelParams := [],
                       type := ← instantiateMVars (← inferType w2a), value := ← instantiateMVars w2a,
                       hints := .opaque, safety := .safe })
example : LeTrocq.Tests.tr33.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl
example : LeTrocq.Tests.tr2a.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl

/- a HIGHER-ORDER domain `(Nat → Nat) → Nat` transfers at (1,0): assembly nests through the arrow domain. -/
run_cmd Command.liftTermElabM do
  let e ← mkArrow (← mkArrow (mkConst ``Nat) (mkConst ``Nat)) (mkConst ``Nat)
  let wit ← transfer e (map1, map0)
  addDecl (.defnDecl { name := `LeTrocq.Tests.trHO, levelParams := [],
                       type := ← instantiateMVars (← inferType wit), value := ← instantiateMVars wit,
                       hints := .opaque, safety := .safe })
example : True := by
  have : Param .map1 .map0 ((Nat → Nat) → Nat) ((Unary → Unary) → Unary) := LeTrocq.Tests.trHO
  trivial

end LeTrocq.Tests
