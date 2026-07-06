# LeTrocq

> **DISCLAIMER:** This page was written by an AI assistant and still needs human polishing and proof-reading.

LeTrocq is a Lean-native, *graded* reformulation of [Trocq](https://arxiv.org/abs/2310.14022)
(Cohen–Crance–Mahboubi) in the no-univalence fragment. Register an equivalence between two types once,
and LeTrocq transports types, terms, and goals across it — generating verified `Param` witnesses whose
transport maps *compute*. Every generated proof is choice-free (`propext` / `Quot.sound`).

| Design aim | What it means |
|---|---|
| **Library-agnostic** | no dependencies beyond Lean core; the driver hardcodes no type (even `List` and the kernel `Quot` are ordinary `@[trocq]` registrations), and ground types need none |
| **Predictable** | one deterministic top-down pass — no typeclass resolution, no backtracking, no constraint-solving fixpoint — so transfer either produces a witness or fails with a definite reason |

## Example

```lean
import LeTrocq
import Examples.NatUnary   -- registers `Nat ≃ Unary` via `@[trocq]`

open LeTrocq.Examples

-- transport a function across the equivalence; the map computes
example : (transfer% (Nat → Nat)).cov.map (· + 1) Unary.z = Unary.s Unary.z := rfl

-- prove a `Unary` goal by transferring it to the easier `Nat` side
example : Unary → Unary := by
  trocq            -- ⊢ Nat → Nat
  exact (· + 1)
```

## Organisation

- **User guide** — [quickstart](guide/quickstart.md), the [surfaces](guide/surfaces.md),
  [registering an equivalence](guide/registering.md), [the standard library](guide/stdlib.md).
- **Design** — the [graded hierarchy](design/hierarchy.md), the [translation](design/translation.md),
  the [combinators](design/combinators.md), the [solver](design/solver.md), the
  [registry](design/registry.md). Each result names the Lean declaration that realises it.
- **Meta** — [soundness](meta/soundness.md), [relation to Trocq](meta/relation-to-trocq.md),
  [limitations](meta/limitations.md).

Source: [github.com/theolaurent/LeTrocq](https://github.com/theolaurent/LeTrocq).
