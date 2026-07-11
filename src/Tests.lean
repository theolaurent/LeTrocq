/-

Test suite entry point (`lake test` driver). Building it compiles all `Tests.*` modules; every
`example`, `#guard_msgs`, and `run_cmd` assertion fires at elaboration, so a regression fails
the build. `main` only runs if everything elaborated.

-/
import Tests.Core.Class
import Tests.Core.Param
import Tests.Combinators.Arrow
import Tests.Combinators.Forall
import Tests.Combinators.Universe
import Tests.Driver.Registry
import Tests.Driver.Counterpart
import Tests.Driver.Tactic
import Tests.Driver.DepFamily
import Tests.Driver.TypeDirected
import Tests.Driver.Record
import Tests.Driver.Group
import Tests.Driver.ListUnit
import Tests.Lib

/-
   axiom-footprint guard (subsumes a `sorry`/`admit` check). Every `LeTrocq.*` declaration is checked.
   which axioms are tolerated differs by layer:
     - object-level content (combinators, witnesses, relators, registered bases) may use `propext`/`Quot.sound`
     - the metaprogram modules additionally tolerates `Classical.choice`, since it runs on `MetaM`
-/

run_cmd Lean.Elab.Command.liftCoreM do
  let env ← Lean.getEnv
  let mods := env.header.moduleNames
  let metaModules : List Lean.Name :=
    [`LeTrocq.Driver.Registry, `LeTrocq.Driver.Counterpart, `LeTrocq.Driver.Transfer, `LeTrocq.Driver.Tactic]
  let baseAllowed : List Lean.Name := [``propext, ``Quot.sound]
  for (name, _) in env.constants.toList do
    if (`LeTrocq).isPrefixOf name then
      -- TODO: move the two lets outside
      let isMeta := match env.getModuleIdxFor? name with
        | some idx => metaModules.contains mods[idx.toNat]!
        | none     => false   -- defined in this (test) module ⇒ object-level
      let allowed := if isMeta then ``Classical.choice :: baseAllowed else baseAllowed
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do
          throwError "axiom guard: `{name}` depends on disallowed axiom `{ax}` (allowed: {allowed})"

def main : IO Unit := IO.println "✓ All LeTrocq tests passed."
