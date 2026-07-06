# Soundness and the axiom footprint

> **DISCLAIMER:** This page was written by an AI assistant and still needs human polishing and proof-reading.

*Source: the `run_cmd` axiom guard in `src/Tests.lean` (fires at `lake test` / CI).*

Every `LeTrocq.*` declaration is checked: a stray `sorry` adds `sorryAx` and any new axiom adds itself, so
either fails the build. The tolerated axioms differ by layer:

| layer | modules | allowed axioms |
|---|---|---|
| **object-level** | everything except the four driver modules — combinators, witnesses, relators, bases, and every `Param` the driver *generates* | `propext`, `Quot.sound` |
| **driver** | `Driver.{Registry,Counterpart,Transfer,Tactic}` | `+ Classical.choice` |

The driver runs on Lean's `MetaM`, which uses choice at its root (as `simp` / `omega` do); that is
compile-time tooling and never enters a generated proof. The object level — including generated witnesses —
is held to the stricter set, so transported mathematics is choice-free up to `propext` / `Quot.sound`.

Transported maps also *compute*: the `example … := rfl` checks pin this down (e.g.
`(transfer% (Nat → Nat)).cov.map (· + 1) Unary.z = Unary.s Unary.z`). Leaf-by-leaf counterparts, rather
than `iso`-conjugation, are what keep reduction unstuck.
