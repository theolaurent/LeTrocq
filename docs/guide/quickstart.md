# Quickstart

## Install

LeTrocq depends only on Lean core (no Mathlib). Add it as a git dependency to your `lakefile.toml`

```toml
[[require]]
name = "letrocq"
git = "https://github.com/theolaurent/LeTrocq.git"
rev = "main"

```

and run `lake update`.

## First transfer

Nothing transfers non-trivially until an equivalence is registered.
`Examples/NatUnary.lean` registers `Nat ≃ Unary`.

```lean
import LeTrocq
import Examples.NatUnary   -- registers `Nat ≃ Unary` via `@[trocq]`

open LeTrocq.Examples

-- transport a function across the equivalence; the map does compute
example : (transfer from (Nat → Nat)).cov.map (· + 1) Unary.z = Unary.s Unary.z := rfl

-- prove a `Unary` goal by transferring it to the `Nat` side
example : Unary → Unary := by
  trocq            -- ⊢ Nat → Nat
  exact (· + 1)
```
