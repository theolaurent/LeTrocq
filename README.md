# LeTrocq

[![CI](https://github.com/theolaurent/LeTrocq/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/theolaurent/LeTrocq/actions/workflows/ci.yml)
[![Documentation](https://github.com/theolaurent/LeTrocq/actions/workflows/docs.yml/badge.svg?branch=main)](https://github.com/theolaurent/LeTrocq/actions/workflows/docs.yml)

A Lean implementation of the [Trocq](https://github.com/rocq-community/trocq)
proof-transfer framework.

Aims at
- library agnosticism: no dependencies beyond Lean core
- predictability: single pass, no typeclass resolution,
  no backtracking, no constraint-solving

## Example

```lean
import LeTrocq
import Examples.NatUnary   -- registers `Nat ≃ Unary` via `@[trocq]`

open LeTrocq.Examples

-- transport a function across the equivalence; the map does compute
example : (transfer% (Nat → Nat)).cov.map (· + 1) Unary.z = Unary.s Unary.z := rfl

-- prove a `Unary` goal by transferring it to the `Nat` side
example : Unary → Unary := by
  trocq            -- ⊢ Nat → Nat
  exact (· + 1)
```

## How it works

Proof transfer relies on a *parametricity translation*, a syntax-directed
construction of relational counterparts of terms and types.

It is threefold:
- a term/type counterpart `⟨t⟩` that rebuilds `t` over the target
- a relational counterpart `⟦A⟧` that build a transport relation between types `A` and `⟨A⟩`
- a relational witness `[t]` that certifies that `⟨t⟩` indeed relates to `t`

See the [documentation](https://theolaurent.github.io/LeTrocq/) for the full account.

## Build

```sh
lake build     # the library
lake test      # test suite + axiom-footprint guard

mdbook build   # the documentation (needs mdbook + mdbook-katex + mdbook-bib)
mdbook serve   # live preview
```
