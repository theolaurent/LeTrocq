/-
Test suite entry point (the `lake test` driver).

Building this executable compiles all `Tests.*` modules; every `example … := rfl`, `#guard_msgs`
axiom-footprint check, and metaprogram `run_cmd` assertion in them fires at elaboration, so a
regression fails the build and hence `lake test`. `main` only runs if everything elaborated.
-/
import Tests.Lattice
import Tests.Hierarchy
import Tests.Core.Arrow
import Tests.Core.Forall
import Tests.Core.Universe
import Tests.Solver
import Tests.Tactic
import Tests.Translate

/- AXIOM-FOOTPRINT GUARD (subsumes a `sorry`/`admit` check). Every `LeTrocq.*` declaration — library, examples,
   and the named test witnesses, all in scope here since this is the test root — may depend ONLY on the three
   standard axioms `propext` / `Classical.choice` / `Quot.sound`. A stray `sorry`/`admit` adds `sorryAx`, and
   any new axiom adds itself; either fails this check, which runs at build time (so `lake test`/CI enforce it).
   (`Classical.choice` enters only through Lean's auto-generated structure boilerplate, e.g. `*.noConfusion` —
   no hand-written `LeTrocq.*` declaration uses it.)
   (`example … := rfl` checks separately guard the computational facts, which a `sorry` couldn't satisfy.) -/
run_cmd Lean.Elab.Command.liftCoreM do
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in (← Lean.getEnv).constants.toList do
    if (`LeTrocq).isPrefixOf name then
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do
          throwError "axiom guard: `{name}` depends on disallowed axiom `{ax}` (allowed: {allowed})"

def main : IO Unit := IO.println "✓ All LeTrocq tests passed."
