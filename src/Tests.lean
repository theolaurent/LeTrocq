/-
Test suite entry point (the `lake test` driver).

Building this executable compiles all `Tests.*` modules; every `example … := rfl`, `#guard_msgs`
axiom-footprint check, and metaprogram `run_cmd` assertion in them fires at elaboration, so a
regression fails the build and hence `lake test`. `main` only runs if everything elaborated.
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
import Tests.Lib

/- AXIOM-FOOTPRINT GUARD (subsumes a `sorry`/`admit` check). EVERY `LeTrocq.*` declaration is checked — a
   stray `sorry`/`admit` adds `sorryAx` and any genuinely new axiom adds itself, so either fails this
   build-time check (so `lake test`/CI enforce it) in BOTH layers. (`example … := rfl` checks separately
   guard the computational facts.)

   What differs is only WHICH standard axioms are tolerated, by layer:
     • OBJECT-LEVEL content — every combinator, witness, relator, registered base, AND every `Param` the
       driver GENERATES (`transferred`/`flagshipWit` below, the `transfer%`/`trocq` outputs) — may use ONLY
       `propext`/`Quot.sound`. NO `Classical.choice`: the math the user transports is choice-free.
     • the DRIVER (the metaprogram modules below) additionally tolerates `Classical.choice`, because it runs
       on Lean's `MetaM`/elaboration API, which uses choice at its root (e.g. `Lean.Meta.inferType`) — exactly
       as `simp`/`omega` do. That choice is compile-time tooling and never enters a generated proof.
   This is a deliberate per-layer policy, NOT a weakening: object-level code is held to the STRICTER set, and
   the driver is still guarded against `sorry`/new axioms — only `Classical.choice` is let through there. -/
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
