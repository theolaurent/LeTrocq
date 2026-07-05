# LeTrocq

**LeTrocq** is a Lean-native, *graded* reformulation of the
[Trocq](https://arxiv.org/abs/2310.14022) parametricity / proof-transfer framework
(Cohen–Crance–Mahboubi), in the **no-univalence** fragment. Register an equivalence between two
types once, and LeTrocq automatically transports types, terms, and goals across it — generating
verified `Param` witnesses whose transport maps *compute*. Every generated proof is choice-free
(only `propext` / `Quot.sound`).

Two design aims set this port apart:

- **Library-agnostic.** No dependencies beyond Lean core, and the driver hardcodes no types — even
  `List` and the kernel constant `Quot` are ordinary `@[trocq]` registrations it reads from an
  environment extension. Ground types (`Nat`, `Bool`, …) need no registration at all: a type that
  transfers to itself is short-circuited to the generic reflexive witness.
- **Predictable.** Transfer is a single deterministic top-down pass — no typeclass resolution, no
  backtracking search, no constraint-solving fixpoint — so it either produces a witness or fails
  with a definite reason.

## Example

```lean
import LeTrocq
import Examples.NatUnary   -- registers `Nat ≃ Unary` via `@[trocq]`

open LeTrocq.Examples

-- transport a function across the equivalence; the map COMPUTES
example : (transfer% (Nat → Nat)).cov.map (· + 1) Unary.z = Unary.s Unary.z := rfl

-- prove a `Unary` goal by transferring it to the easier `Nat` side
example : Unary → Unary := by
  trocq            -- ⊢ Nat → Nat
  exact (· + 1)
```

## How this book is organised

- The **user guide** is the practical side: how to [get started](guide/quickstart.md), the four
  [user surfaces](guide/surfaces.md) (`transfer%` / `trocq` / `translate%` / `relate%`), how to
  [register your own equivalence](guide/registering.md), and what ships in
  [the standard library](guide/stdlib.md).
- The **design** part is the formal account: [the graded parametricity
  translation](design/translation.md) (the hierarchy, the combinators, grading) and [the
  demand-driven witness solver](design/solver.md) (the single top-down pass that produces the
  witnesses). It is a faithful port of the project's design blueprint; each result names the Lean
  declaration that realises it.

The source lives at [github.com/theolaurent/LeTrocq](https://github.com/theolaurent/LeTrocq).
