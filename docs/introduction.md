
# LeTrocq

LeTrocq is a Lean reformulation of the [Trocq](https://github.com/rocq-community/trocq)
proof-transfer framework. Register relations between types and terms,
and LeTrocq transports goals across it, generating verified witnesses whose
transport maps compute.

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
