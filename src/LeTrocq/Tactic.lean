/-
The USER SURFACE: the four elaborators/tactics, on top of the driver (`Solver` + `Translate`).

  • `transfer% T`  elaborates to the relatedness witness `Param (4,4) T T'` for a type `T` built over
    a registered base — exposing the generated counterpart `T'` and its transport maps
    (`(transfer% (Nat → Nat)).cov.map` is the transported function `(Nat→Nat) → (Unary→Unary)`).

  • `trocq`  transfers the current goal `G` to its counterpart `G'` (seeded at the comap class (0,1))
    and refines `G` by the backward transport `G' → G`, leaving you to prove `G'`.

  • `translate% t`  ⤳ the `B`-side counterpart `t'`; `relate% t` ⤳ its relatedness `tR : 〚T〛 t t'`.

Everything reads its registries from the `@[trocq]` environment extension; every registered base is available
in both directions (forward, and backward via `Param.sym`), so a goal/term over either side of an equivalence
resolves by head match. Nothing here is tied to a particular base.
-/
import LeTrocq.Transfer
import LeTrocq.TranslateTerm
import Lean
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic
namespace LeTrocq

open MapClass LeTrocq.Translate

/-- `transfer% T` ⤳ the relatedness witness `Param (4,4) T T'` (`T` a type over a registered base). An
    optional `to T'` DEMANDS a specific target `T'` (type-directed selection of the registered bases,
    disambiguating a source with several registered equivalences); without it the preferred base is used. -/
syntax (name := transferStx) "transfer% " term (" to " term)? : term

elab_rules : term
  | `(transfer% $t $[to $tgt?]?) => do
      let tE ← elabType t
      -- force pending elaboration (e.g. a type-family argument's body) so the pass sees a fully-formed type.
      synthesizeSyntheticMVarsNoPostponing
      let target? ← match tgt? with
        | none => pure none
        | some g => do
            let t' ← elabType g
            synthesizeSyntheticMVarsNoPostponing
            pure (some (← instantiateMVars t'))
      let wit ← Transfer.transfer (← instantiateMVars tE) (map4, map4) target?
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
      let wit ← Transfer.transfer goalTy (map0, map1) target?
      let goalTy' := (← instantiateMVars (← inferType wit)).getAppArgs[3]!
      if let some tgtTy := target? then
        unless ← isDefEq goalTy' (← instantiateMVars tgtTy) do
          throwError "trocq: produced counterpart {goalTy'} does not match requested target {tgtTy}"
      -- backward transport `G' → G` = the contra map at class (0,1) (`MapHas map1` is `Map1Has`).
      let backMap ← mkAppM ``Map1Has.map #[← mkAppM ``Param.contra #[wit]]
      let newGoal ← mkFreshExprMVar goalTy'
      g.assign (.app backMap newGoal)
      replaceMainGoal [newGoal.mvarId!]

/-- `translate% t` ⤳ the `B`-side counterpart `⟨t⟩` (rebuilt over `B` leaf-by-leaf, not iso-conjugation). -/
elab "translate% " t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars (← Translate.term (← buildCtx) [] (← instantiateMVars e) none)

/-- `relate% t` ⤳ the relatedness `[t] : 〚T〛 t ⟨t⟩` — the proof the counterpart is correct. -/
elab "relate% " t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars (← Transfer.relate (← instantiateMVars e))

end LeTrocq
