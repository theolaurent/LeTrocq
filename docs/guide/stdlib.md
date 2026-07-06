# The standard library

> **DISCLAIMER:** This page was written by an AI assistant and still needs human polishing and proof-reading.

`import LeTrocq` ships `@[trocq]` registrations for Lean's prelude types, so transfer over them works out
of the box. These are ordinary user-level registrations — they sit in the library only because their
types are in the prelude. The driver knows no type intrinsically; even the kernel constant `Quot`
registers here.

| Module (`LeTrocq/Lib/`) | Type | Notes |
|---|---|---|
| `List`   | `List`   | relator + inductive relation + constructor primitives |
| `Option` | `Option` | the same recipe, smaller |
| `Array`  | `Array`  | reuses `List` through `toList` |
| `Prod`   | `Prod` (×) | two type parameters, non-dependent |
| `Sum`    | `Sum` (⊕)  | two type parameters, two constructors |
| `Sigma`  | `Sigma` (Σ) | dependent — the type-family relator machinery |
| `Quot`   | `Quot`   | kernel quotient: type former + constructor + graded relator |
| `Eq`     | `Eq`     | propositional equality, as a relator over the related type |
| `Logic`  | `Not` / `And` / `Or` / `Iff` | the connectives, as `Prop` relators |

Each type's variance table is in [the combinators](../design/combinators.md#the-lib-relators).

## Ground types

`Bool`, `Nat`, `Empty`, `Unit`, `True`, `False` have no registration file: the whole-diagonal
short-circuit (`paramRefl`) handles them, and a composite over only-diagonal parts (e.g. `Nat × Bool`)
short-circuits as one whole.

## Non-prelude examples

`Examples/` holds registrations a user would write: `NatUnary.lean` (the base `Nat ≃ Unary`, term and
recursor primitives, a predicate relator) and `WTree.lean` (a W-tree exercising the type-family
machinery, including a non-adjacent family domain and a contravariant fiber).
