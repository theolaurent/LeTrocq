/-
The USER SURFACE: the four elaborators/tactics, on top of the driver (`Transfer` + `Counterpart`).

  • `transfer from A`  elaborates to the witness `Param (4,4) A ⟨A⟩` (`A` the SOURCE, counterpart
    synthesized) — exposing the transport maps (`(transfer from (Nat → Nat)).cov.map` is `(Nat→Nat) →
    (Unary→Unary)`). `transfer to B` is the mirror: `Param (4,4) ⟨B⟩ B` (`B` the TARGET, source synthesized).
    An optional `... to B` on the `from` form demands a specific target.

  • `trocq`  treats the goal `G` as the TARGET and its counterpart `G'` as the SOURCE: it assembles
    `Param (1,0) G' G` and refines `⊢ G` by the covariant map `G' → G`, leaving you to prove `G'`.

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
      let A ← instantiateMVars tE
      -- the TARGET `B`: named via `to B`, else the synthesized counterpart `⟨A⟩`.
      let B ← match tgt? with
        | some g => do
            let t' ← elabType g
            synthesizeSyntheticMVarsNoPostponing
            instantiateMVars t'
        | none => Driver.Transfer.counterpart A
      let wit ← Driver.Transfer.transferType A B (map4, map4)
      return (← instantiateMVars wit)
  | `(transfer to $tgt) => do
      let tgtE ← elabType tgt
      synthesizeSyntheticMVarsNoPostponing
      let B ← instantiateMVars tgtE
      -- name the TARGET `B`; synthesize the SOURCE `A = ⟨B⟩`, then assemble the two-ended `Param (4,4) A B`.
      let A ← Driver.Transfer.counterpart B
      let wit ← Driver.Transfer.transferType A B (map4, map4)
      return (← instantiateMVars wit)

/-- `trocq` transfers the goal (the TARGET) across the registered base and leaves you the (easier) counterpart
    SOURCE. An optional `to G'` names that source goal `G'` explicitly (else it is synthesized as `⟨G⟩`); the
    two-ended assembly of `Param G' G` then fails if `G'` is not a valid counterpart of the goal. -/
syntax (name := trocqStx) "trocq" (" to " term)? : tactic

elab_rules : tactic
  | `(tactic| trocq $[to $tgt?]?) => do
      let g ← getMainGoal
      let goalTy ← g.getType
      -- the goal `G` is the TARGET; the SOURCE is the (easier) counterpart `G'` — named via `to G'`, else `⟨G⟩`.
      let goalTy' ← match tgt? with
        | some tgt => instantiateMVars (← Lean.Elab.Tactic.elabTerm tgt none)
        | none => Driver.Transfer.counterpart goalTy
      -- assemble `Param (1,0) G' G` (source `G'`, target `G`); its COVARIANT map `G' → G` refines the goal
      -- `⊢ G` to the (easier) `⊢ G'`.
      let wit ← Driver.Transfer.transferType goalTy' goalTy (map1, map0)
      let fwdMap ← mkAppM ``Map1Has.map #[← mkAppM ``Param.cov #[wit]]
      let newGoal ← mkFreshExprMVar goalTy'
      g.assign (.app fwdMap newGoal)
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
