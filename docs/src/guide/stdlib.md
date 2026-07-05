# The standard library

`import LeTrocq` ships `@[trocq]` registrations for Lean's prelude types, so transfer over them works
out of the box. These are ordinary user-level registrations (each could live verbatim in a downstream
project); they sit in the library only because their types are in the prelude. **The driver knows no
type intrinsically** — even the kernel constant `Quot` registers here via `@[trocq]`.

| Module (`LeTrocq/ParamLib/`) | Type | Notes |
|---|---|---|
| `List`   | `List`   | relator + inductive relation + constructor primitives |
| `Option` | `Option` | the same recipe, smaller |
| `Array`  | `Array`  | reuses `List` through `toList`; literal head `List.toArray` |
| `Prod`   | `Prod` (×) | two type parameters, non-dependent |
| `Sum`    | `Sum` (⊕)  | two type parameters, two constructors |
| `Sigma`  | `Sigma` (Σ) | dependent — exercises the type-**family** relator machinery |
| `Quot`   | `Quot`   | the kernel quotient: type former + constructor + graded relator |
| `Eq`     | `Eq`     | propositional equality, as a relator over the related type |
| `Logic`  | `Not` / `And` / `Or` / `Iff` | the connectives, as `Prop` relators |

## Ground types

There is **no** registration file for `Bool`, `Nat`, `Empty`, `Unit`, `True`, or `False`. They need
none: a type or term whose counterpart is itself is short-circuited to the generic diagonal
`paramRefl` in the driver, so they transfer to themselves — and a user equivalence like `Nat ≃ Unary`
overrides that diagonal whenever it applies. A composite over only-diagonal parts (say `Nat × Bool`)
is itself diagonal, so the whole type short-circuits as one, rather than going through the per-type
relators.

## Non-prelude examples

`Examples/` holds registrations a *user* would write:

- `Examples/NatUnary.lean` — the base equivalence `Nat ≃ Unary`, its term primitives, a recursor
  primitive, and a predicate relator.
- `Examples/DepParam.lean` — a W-tree, showing the type-family relator machinery on a user inductive
  (including a family whose domain is not the adjacent type argument).
