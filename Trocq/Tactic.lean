/-
The USER SURFACE: the four elaborators/tactics, on top of the driver (`Solver` + `Translate`).

  • `transfer% T`  elaborates to the relatedness witness `Param (4,4) T T'` for a type `T` built over
    a registered base — exposing the generated counterpart `T'` and its transport maps
    (`(transfer% (Nat → Nat)).cov.map` is the transported function `(Nat→Nat) → (Unary→Unary)`).

  • `trocq`  transfers the current goal `G` to its counterpart `G'` (seeded at the comap class (0,1))
    and refines `G` by the backward transport `G' → G`, leaving you to prove `G'`.

  • `translate% t`  ⤳ the native `B`-side counterpart `t'`; `relate% t` ⤳ its relatedness `tR : ⟦T⟧ t t'`.
    These live HERE (not in `Translate`) because they hand `Translate.param` the solver's carrier builder
    (`Solver.transfer`) via `Ctx` — so `Translate` need not depend on `Solver`. See `AGENTS.md`.

Everything reads its registries from the `@[trocq]` environment extension; every registered base is available
in both directions (forward, and backward via `Param.sym`), so a goal/term over either side of an equivalence
resolves by head match. Nothing here is tied to a particular base.
-/
import Trocq.Solver
import Trocq.Translate
import Lean
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic
namespace Trocq

open MapClass Trocq.Translate

/-- the carrier builder injected into `Translate`'s `Ctx`: build `Param (4,4) ty ty'` for any carrier `ty`
    (used by `param`'s `Quot.lift` case). This is the surface's half of the `param`↔`transfer` recursion. -/
def carrierBuilder (ty : Expr) : MetaM Expr := return (← Solver.transfer ty (map4, map4)).1

/-- `transfer% T` ⤳ the relatedness witness `Param (4,4) T T'` (`T` a type over a registered base). -/
elab "transfer% " t:term : term => do
  let tE ← elabType t
  -- force pending elaboration (e.g. a type-family argument's body) so `gen` sees a fully-formed type.
  synthesizeSyntheticMVarsNoPostponing
  let (wit, _, _) ← Solver.transfer (← instantiateMVars tE) (map4, map4)
  return (← instantiateMVars wit)

/-- `trocq` transfers the goal across the registered base and leaves you the (easier) counterpart. -/
elab "trocq" : tactic => do
  let g ← getMainGoal
  let goalTy ← g.getType
  let (wit, _, _) ← Solver.transfer goalTy (map0, map1)
  let goalTy' := (← instantiateMVars (← inferType wit)).getAppArgs[3]!
  -- backward transport `G' → G` = the contra map at class (0,1) (`MapHas map1` is `Map1Has`).
  let backMap ← mkAppM ``Map1Has.map #[← mkAppM ``Param.contra #[wit]]
  let newGoal ← mkFreshExprMVar goalTy'
  g.assign (.app backMap newGoal)
  replaceMainGoal [newGoal.mvarId!]

/-- `translate% t` ⤳ the native `B`-side counterpart `t'` (rebuilt over `B`, not iso-conjugation). -/
elab "translate% " t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let (e', _) ← param (← buildCtx carrierBuilder) [] (← instantiateMVars e)
  instantiateMVars e'

/-- `relate% t` ⤳ the relatedness `tR : ⟦T⟧ t t'` — the proof the native counterpart is correct. -/
elab "relate% " t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let (_, eR) ← param (← buildCtx carrierBuilder) [] (← instantiateMVars e)
  instantiateMVars eR

end Trocq
