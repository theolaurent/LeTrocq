# Quickstart

> **DISCLAIMER:** This page was written by an AI assistant and still needs human polishing and proof-reading.

## Install

LeTrocq depends only on Lean core (no Mathlib). Add it as a git dependency, then:

```lean
import LeTrocq
```

That import brings in the driver and the prelude registrations ([standard library](stdlib.md)).

## Build

```sh
lake build   # warnings are errors
lake test    # test suite + axiom-footprint guard
```

`lake test` enforces, in one shot, `warningAsError`, every `example … := rfl` check, and the
[axiom guard](../meta/soundness.md) (generated proofs use only `propext` / `Quot.sound`).

## First transfer

Nothing transfers non-trivially until an equivalence is registered; `Examples/NatUnary.lean` registers
`Nat ≃ Unary`.

```lean
import LeTrocq
import Examples.NatUnary
open LeTrocq.Examples

-- `transfer% T` exposes the counterpart and its maps; the forward map computes:
example : (transfer% (Nat → Nat)).cov.map (· + 1) Unary.z = Unary.s Unary.z := rfl

-- `trocq` rewrites the goal to its counterpart on the other side:
example : Unary → Unary := by
  trocq            -- ⊢ Nat → Nat
  exact (· + 1)
```

A registered base works in both directions (the backward reading is `Param.sym`), so a goal or term over
either side resolves by head match.

Next: [the surfaces](surfaces.md), [registering your own equivalence](registering.md).
