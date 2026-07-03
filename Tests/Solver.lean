/- The driver: Expr → demand-driven `assemble` → witness, end to end. `Transfer.assemble` walks the type once,
   pushing a demanded class top-down through the dependency tables and building each node's `Param` at the minimal
   class the demand dictates (no constraint graph, no fixpoint — bidir_solver.md). -/
import Lean
import LeTrocq
import Examples.NatUnary
open Lean Lean.Meta Lean.Elab Lean.Elab.Command
namespace LeTrocq.Tests
open LeTrocq LeTrocq.Transfer MapClass LeTrocq.Examples

def flagshipTy := ∀ A : Type, A → A

/- generate the witness for `Nat → Nat` at root (1,0), then hard-check it. It is built by the GRADED `paramArrow`
   at the per-node minimal class (`arrowVariance (1,0)` ⇒ domain at (0,1), codomain at (1,0)) — no build-(3,3)-then-weaken. -/
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

/- MAP_TYPE: the same `∀ A : Type, A → A` at root (2b,0). The OUTER class of the universe is `forallVariance (2b,0).1 =
   (0,2a)` (≤ the (2a,2a) ceiling, so it assembles without univalence); the bound variable `A` is offered at
   INNER class (4,4) — the pinned top, independent of the capped outer (`paramTypeAtInner` carries it). -/
run_cmd Command.liftTermElabM do
  let e := (← getConstInfo ``flagshipTy2).value!
  let wit ← transfer e (map2b, map0)
  let ty ← instantiateMVars (← inferType wit)
  addDecl (.defnDecl { name := `LeTrocq.Tests.flagshipWit2b, levelParams := [], type := ty, value := wit,
                       hints := .opaque, safety := .safe })
example : True := by
  have : Param .map2b .map0 (∀ A : Type, A → A) (∀ A : Type, A → A) := LeTrocq.Tests.flagshipWit2b
  trivial

/- UNIVERSE POLYMORPHISM: the universe combinator now carries the ACTUAL level, so `∀ A : Type w, A → A`
   transfers at any `w`, not just `w = 0`. Under the old `Type 0`-pinned binder this mismatched the real
   `Type 2` binder and assembly failed. -/
def flagshipTy2Lvl2 := ∀ A : Type 2, A → A
run_cmd Command.liftTermElabM do
  let e := (← getConstInfo ``flagshipTy2Lvl2).value!
  let wit ← transfer e (map0, map1)
  addDecl (.defnDecl { name := `LeTrocq.Tests.flagshipWitLvl2, levelParams := [],
                       type := ← instantiateMVars (← inferType wit), value := ← instantiateMVars wit,
                       hints := .opaque, safety := .safe })
example : True := by
  have : Param .map0 .map1 (∀ A : Type 2, A → A) (∀ A : Type 2, A → A) := LeTrocq.Tests.flagshipWitLvl2
  trivial

/- and a genuinely universe-POLYMORPHIC input (a level PARAM `u`, not a literal): the level arrives as a
   `Level.param` and is PRESERVED (`defaultFreeLevels` zeroes only mvars). The generated witness is itself
   universe-polymorphic — instantiated here at level 5. -/
universe u
def flagshipTyU := ∀ A : Type u, A → A
run_cmd Command.liftTermElabM do
  let ci ← getConstInfo ``flagshipTyU
  let wit ← transfer ci.value! (map0, map1)
  addDecl (.defnDecl { name := `LeTrocq.Tests.flagshipWitU, levelParams := ci.levelParams,
                       type := ← instantiateMVars (← inferType wit), value := ← instantiateMVars wit,
                       hints := .opaque, safety := .safe })
example : True := by
  have : Param .map0 .map1 (∀ A : Type 5, A → A) (∀ A : Type 5, A → A) := LeTrocq.Tests.flagshipWitU.{5}
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
