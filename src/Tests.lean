/-
Test suite entry point (the `lake test` driver). Building it compiles all `Tests.*` modules; every
`example … := rfl`, `#guard_msgs`, and `run_cmd` assertion fires at elaboration, so a regression fails
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

/- AXIOM-FOOTPRINT GUARD (subsumes a `sorry`/`admit` check). Every `LeTrocq.*` declaration is checked; a
   stray `sorry` or any new axiom fails this build-time check. Which standard axioms are tolerated differs
   by layer:
     • OBJECT-LEVEL content (combinators, witnesses, relators, registered bases, AND the `Param`s the driver
       generates) may use ONLY `propext`/`Quot.sound` — the transported math is choice-free.
     • the DRIVER (the metaprogram modules) additionally tolerates `Classical.choice`, since it runs on
       `MetaM`, which uses choice at its root (as `simp`/`omega` do); that choice is compile-time tooling and
       never enters a generated proof.
   Deliberate per-layer policy: object-level held to the stricter set, driver still guarded against `sorry`/
   new axioms. -/
run_cmd Lean.Elab.Command.liftCoreM do
  let env ← Lean.getEnv
  let mods := env.header.moduleNames
  -- the metaprogramming layer (irreducibly `Classical.choice`-using via `MetaM`); everything else is math.
  let metaModules : List Lean.Name :=
    [`LeTrocq.Driver.Registry, `LeTrocq.Driver.Counterpart, `LeTrocq.Driver.Transfer, `LeTrocq.Driver.Tactic]
  let baseAllowed : List Lean.Name := [``propext, ``Quot.sound]
  for (name, _) in env.constants.toList do
    if (`LeTrocq).isPrefixOf name then
      let isMeta := match env.getModuleIdxFor? name with
        | some idx => metaModules.contains mods[idx.toNat]!
        | none     => false   -- defined in this (test) module ⇒ object-level
      let allowed := if isMeta then ``Classical.choice :: baseAllowed else baseAllowed
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do
          throwError "axiom guard: `{name}` depends on disallowed axiom `{ax}` (allowed: {allowed})"

def main : IO Unit := IO.println "✓ All LeTrocq tests passed."
