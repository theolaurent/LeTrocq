/-
The USER SURFACE: the `transfer%` term elaborator and the `trocq` tactic, on top of the driver.

  • `transfer% T`  elaborates to the relatedness witness `Param (4,4) T T'` for a type `T` built over
    a registered base — exposing the generated counterpart `T'` and its transport maps
    (`(transfer% (Nat → Nat)).cov.map` is the transported function `(Nat→Nat) → (Unary→Unary)`).

  • `trocq`  transfers the current goal `G` to its counterpart `G'` (seeded at the comap class (0,1))
    and refines `G` by the backward transport `G' → G`, leaving you to prove `G'`.

Both read their registries from the `@[trocq]` environment extension (`Solver.buildAtoms`/`buildConsts`):
every registered base is available in both directions (forward, and backward via `Param.sym`), so a goal
over either side of an equivalence resolves by head match. Nothing here is tied to a particular base.
-/
import Trocq.Solver
import Lean
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic
namespace Trocq

open MapClass

/-- `transfer% T` ⤳ the relatedness witness `Param (4,4) T T'` (`T` a type over a registered base). -/
elab "transfer% " t:term : term => do
  let tE ← elabType t
  let (wit, _, _) ← Solver.transfer (← Solver.buildAtoms) (← Solver.buildConsts) tE (map4, map4)
  return (← instantiateMVars wit)

/-- `trocq` transfers the goal across the registered base and leaves you the (easier) counterpart. -/
elab "trocq" : tactic => do
  let g ← getMainGoal
  let goalTy ← g.getType
  let (wit, _, _) ← Solver.transfer (← Solver.buildAtoms) (← Solver.buildConsts) goalTy (map0, map1)
  let goalTy' := (← instantiateMVars (← inferType wit)).getAppArgs[3]!
  -- backward transport `G' → G` = the contra map at class (0,1) (`MapHas map1` is `Map1Has`).
  let backMap ← mkAppM ``Map1Has.map #[← mkAppM ``Param.contra #[wit]]
  let newGoal ← mkFreshExprMVar goalTy'
  g.assign (.app backMap newGoal)
  replaceMainGoal [newGoal.mvarId!]

end Trocq
