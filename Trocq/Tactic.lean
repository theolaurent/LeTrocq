/-
The USER SURFACE: the `transfer%` term elaborator and the `trocq` tactic, on top of the driver.

  • `transfer% T`  elaborates to the relatedness witness `Param (4,4) T T'` for a type `T` built over
    the registered base — exposing the generated counterpart `T'` and its transport maps
    (`(transfer% (Nat → Nat)).cov.map` is the transported function `(Nat→Nat) → (Unary→Unary)`).

  • `trocq`  transfers the current goal `G` to its counterpart `G'` (seeded at the comap class (0,1))
    and refines `G` by the backward transport `G' → G`, leaving you to prove `G'`.

The registered base is still hard-wired to `Nat ≃ Unary` (the `@[trocq]` attribute that lets users
register their own bases is the next milestone). `transfer%` reads it forward (`Nat ↦ Unary`); `trocq`
reads it backward (`Unary ↦ Nat`, via `Param.sym`) so a `Unary` goal reduces to the easier `Nat` one.
-/
import Trocq.Solver
import Lean
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic
namespace Trocq

/-- the registered base read backward, `Unary ≃ Nat`, for goal transfer. -/
def RNsym : Param MapClass.map4 MapClass.map4 Unary Nat := RN.sym

namespace Solver
/-- atoms registering `Unary ↦ Nat` (the goal side) for the `trocq` tactic. -/
def symAtoms : NameMap (Expr × Expr × ParamClass) :=
  (mkNameMap _).insert ``Unary (mkConst ``Nat, mkConst ``RNsym, (MapClass.map4, MapClass.map4))
end Solver

/-- `transfer% T` ⤳ the relatedness witness `Param (4,4) T T'` (`T` a type over the registered base). -/
elab "transfer% " t:term : term => do
  let tE ← elabType t
  let (wit, _, _) ← Solver.transfer Solver.demoAtoms tE (MapClass.map4, MapClass.map4)
  return (← instantiateMVars wit)

/-- `trocq` transfers the goal across the registered base and leaves you the (easier) counterpart. -/
elab "trocq" : tactic => do
  let g ← getMainGoal
  let goalTy ← g.getType
  let (wit, _, _) ← Solver.transfer Solver.symAtoms goalTy (MapClass.map0, MapClass.map1)
  let goalTy' := (← instantiateMVars (← inferType wit)).getAppArgs[3]!
  -- backward transport `G' → G` = the contra map at class (0,1) (`MapHas map1` is `Map1Has`).
  let backMap ← mkAppM ``Map1Has.map #[← mkAppM ``Param.contra #[wit]]
  let newGoal ← mkFreshExprMVar goalTy'
  g.assign (.app backMap newGoal)
  replaceMainGoal [newGoal.mvarId!]

end Trocq
