# Quickstart

## Getting the library

LeTrocq depends only on Lean core — no Mathlib. Add it to your `lakefile` as a git dependency (or
clone and build it directly), then `import LeTrocq`:

```lean
import LeTrocq
```

That single import brings the driver into scope together with the standard-library registrations for
the prelude types (`List`, `Option`, `Array`, `Prod`, `Sum`, `Sigma`, `Quot`, `Eq`, and the logical
connectives — see [The standard library](stdlib.md)).

## Building

```sh
lake build   # warnings are errors
lake test    # the test suite + the axiom-footprint guard
```

`lake test` compiles the whole codebase (library + examples + tests) and enforces, in one shot,
`warningAsError`, every `example … := rfl` regression check, and the axiom guard (every generated
`LeTrocq.*` proof may use only `propext` / `Quot.sound`).

## Your first transfer

Nothing transfers non-trivially until you register an equivalence. The worked example
`Examples/NatUnary.lean` registers `Nat ≃ Unary` (unary naturals):

```lean
import LeTrocq
import Examples.NatUnary

open LeTrocq.Examples

-- `transfer% T` exposes the counterpart type `T'` and its transport maps.
-- The forward map COMPUTES, so this is `rfl`:
example : (transfer% (Nat → Nat)).cov.map (· + 1) Unary.z = Unary.s Unary.z := rfl

-- `trocq` rewrites the current goal to its counterpart on the other side of the equivalence:
example : Unary → Unary := by
  trocq            -- ⊢ Nat → Nat
  exact (· + 1)
```

Because a registered base is available in *both* directions (the driver derives the backward reading
via `Param.sym`), a goal or term over *either* side of an equivalence resolves by head match.

## Where to go next

- [The user surfaces](surfaces.md) — the four elaborators/tactics in detail.
- [Registering your own equivalence](registering.md) — the recipe for `@[trocq]`.
- [The graded parametricity translation](../design/translation.md) — how it works underneath.
