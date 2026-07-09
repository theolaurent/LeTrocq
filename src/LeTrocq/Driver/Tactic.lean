/-
The USER SURFACE: the four elaborators/tactics, on top of the driver (`Transfer` + `Counterpart`).

  • `transfer from A`  elaborates to the witness `Param (4,4) A ⟨A⟩` (`A` the SOURCE, counterpart
    synthesized) — exposing the transport maps (`(transfer from (Nat → Nat)).cov.map` is `(Nat→Nat) →
    (Unary→Unary)`). `transfer to B` is the mirror: `Param (4,4) ⟨B⟩ B` (`B` the TARGET, source synthesized).
    An optional `... to B` on the `from` form demands a specific target.

  • `trocq`  transfers the current goal `G` to its counterpart `G'` (seeded at the comap class (0,1))
    and refines `G` by the backward transport `G' → G`, leaving you to prove `G'`.

  • `translate t`  ⤳ the `B`-side counterpart `t'`; `relate t` ⤳ its relatedness `tR : 〚T〛 t t'`.

Everything reads its registries from the `@[trocq]` environment extension; every registered base is available
in both directions (forward, and backward via `Param.sym`), so a goal/term over either side of an equivalence
resolves by head match. Nothing here is tied to a particular base.
-/
import LeTrocq.Driver.Transfer
import LeTrocq.Driver.Counterpart
import Lean
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic
namespace LeTrocq

open MapClass LeTrocq.Counterpart

/-- `transfer from A` ⤳ the witness `Param (4,4) A ⟨A⟩` (`A` the SOURCE, counterpart synthesized). An
    optional `to B` DEMANDS a specific target `B` (type-directed base selection, disambiguating a source
    with several registered equivalences). -/
syntax (name := transferFromStx) "transfer " "from " term (" to " term)? : term
/-- `transfer to B` ⤳ the mirror witness `Param (4,4) ⟨B⟩ B` (`B` the TARGET; the SOURCE is synthesized by
    the counterpart translation, using the last-registered counterpart per head). -/
syntax (name := transferToStx) "transfer " "to " term : term

elab_rules : term
  | `(transfer from $t $[to $tgt?]?) => do
      let tE ← elabType t
      -- force pending elaboration (e.g. a type-family argument's body) so the pass sees a fully-formed type.
      synthesizeSyntheticMVarsNoPostponing
      let target? ← match tgt? with
        | none => pure none
        | some g => do
            let t' ← elabType g
            synthesizeSyntheticMVarsNoPostponing
            pure (some (← instantiateMVars t'))
      let wit ← Driver.Transfer.transferType (← instantiateMVars tE) (map4, map4) target?
      return (← instantiateMVars wit)
  | `(transfer to $tgt) => do
      let tgtE ← elabType tgt
      synthesizeSyntheticMVarsNoPostponing
      let tgtE ← instantiateMVars tgtE
      -- synthesize the SOURCE `⟨B⟩` (the last-registered counterpart per head), then transfer forward in
      -- CHECK mode (target `B` guides base selection; the witness's right side is `B`).
      let src ← Counterpart.term (← buildCtx) [] tgtE none
      let wit ← Driver.Transfer.transferType (← instantiateMVars src) (map4, map4) (some tgtE)
      return (← instantiateMVars wit)

/-- `trocq` transfers the goal across the registered base and leaves you the (easier) counterpart. An
    optional `to G'` demands a specific target goal `G'` (type-directed base selection); the produced
    counterpart must then match `G'` (checked by `isDefEq`). -/
syntax (name := trocqStx) "trocq" (" to " term)? : tactic

elab_rules : tactic
  | `(tactic| trocq $[to $tgt?]?) => do
      let g ← getMainGoal
      let goalTy ← g.getType
      let target? ← match tgt? with
        | none => pure none
        | some tgt => pure (some (← Lean.Elab.Tactic.elabTerm tgt none))
      let wit ← Driver.Transfer.transferType goalTy (map0, map1) target?
      let goalTy' := (← instantiateMVars (← inferType wit)).getAppArgs[3]!
      if let some tgtTy := target? then
        unless ← isDefEq goalTy' (← instantiateMVars tgtTy) do
          throwError "trocq: produced counterpart {goalTy'} does not match requested target {tgtTy}"
      -- backward transport `G' → G` = the contra map at class (0,1) (`MapHas map1` is `Map1Has`).
      let backMap ← mkAppM ``Map1Has.map #[← mkAppM ``Param.contra #[wit]]
      let newGoal ← mkFreshExprMVar goalTy'
      g.assign (.app backMap newGoal)
      replaceMainGoal [newGoal.mvarId!]

/-- `translate t` ⤳ the `B`-side counterpart `⟨t⟩` (rebuilt over `B` leaf-by-leaf, not iso-conjugation). -/
elab "translate " t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars (← Counterpart.term (← buildCtx) [] (← instantiateMVars e) none)

/-- `relate t` ⤳ the relatedness `[t] : 〚T〛 t ⟨t⟩` — the proof the counterpart is correct. -/
elab "relate " t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars (← Driver.Transfer.relateTerm (← instantiateMVars e))

end LeTrocq
