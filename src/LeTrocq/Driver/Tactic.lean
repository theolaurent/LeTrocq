/-
The user surface: four elaborators/tactics over the driver (`Transfer` + `Counterpart`).
  • `transfer from A` / `transfer to B` / `transfer from A to B`
    build the witness `Param (4,4) A ⟨A⟩` / `Param (4,4) ⟨B⟩ B` / `Param (4,4) A B`.
  • `trocq` treats the goal `G` as the target, assembles `Param (1,0) ⟨G⟩ G`, and refines `⊢ G` by the
    (covariant) map `⟨G⟩ → G`, leaving the (easier?) `⊢ ⟨G⟩`.
  • `translate t` builds counterpart `⟨t⟩`; `relate t` builds relatedness `[t] : 〚T〛 t ⟨t⟩`.

All registries come from the `@[trocq]` extension; every base is available both directions (via `Param.sym`),
so either side of an equivalence resolves by head match.
-/
import LeTrocq.Driver.Transfer
import LeTrocq.Driver.Counterpart
import Lean
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic
namespace LeTrocq

open MapClass LeTrocq.Counterpart

/-- `transfer from A` ⤳ `Param (4,4) A ⟨A⟩`; optional `to B` demands a specific target (disambiguates a
    source with several registered equivalences). -/
syntax (name := transferFromStx) "transfer " "from " term (" to " term)? : term
/-- `transfer to B` ⤳ the mirror `Param (4,4) ⟨B⟩ B` (`B` the TARGET, source synthesized). -/
syntax (name := transferToStx) "transfer " "to " term : term

elab_rules : term
  | `(transfer from $t $[to $tgt?]?) => do
      let tE ← elabType t
      -- force pending elaboration so the pass sees a fully-formed type.
      synthesizeSyntheticMVarsNoPostponing
      let A ← instantiateMVars tE
      -- TARGET `B`: named via `to B`, else the synthesized counterpart `⟨A⟩`.
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
      -- synthesize the SOURCE `A = ⟨B⟩`, then assemble `Param (4,4) A B`.
      let A ← Driver.Transfer.counterpart B
      let wit ← Driver.Transfer.transferType A B (map4, map4)
      return (← instantiateMVars wit)

/-- `trocq` transfers the goal (the TARGET) and leaves you the (easier) counterpart source; optional `to G'`
    names that source explicitly (else `⟨G⟩`). -/
syntax (name := trocqStx) "trocq" (" to " term)? : tactic

elab_rules : tactic
  | `(tactic| trocq $[to $tgt?]?) => do
      let g ← getMainGoal
      let goalTy ← g.getType
      -- SOURCE `G'`: named via `to G'`, else `⟨G⟩`.
      let goalTy' ← match tgt? with
        | some tgt => instantiateMVars (← Lean.Elab.Tactic.elabTerm tgt none)
        | none => Driver.Transfer.counterpart goalTy
      -- `Param (1,0) G' G`; its COVARIANT map `G' → G` refines `⊢ G` to the easier `⊢ G'`.
      let wit ← Driver.Transfer.transferType goalTy' goalTy (map1, map0)
      let fwdMap ← mkAppM ``Map1.map #[← mkAppM ``Param.cov #[wit]]
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
