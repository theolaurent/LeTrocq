/-
Test suite entry point (the `lake test` driver).

Building this executable compiles all `Tests.*` modules; every `example … := rfl`, `#guard_msgs`
axiom-footprint check, and metaprogram `run_cmd` assertion in them fires at elaboration, so a
regression fails the build and hence `lake test`. `main` only runs if everything elaborated.
-/
import Tests.Lattice
import Tests.Hierarchy
import Tests.Combinators.Arrow
import Tests.Combinators.Forall
import Tests.Combinators.Universe
import Tests.Solver
import Tests.Tactic

def main : IO Unit := IO.println "✓ All Trocq tests passed."
