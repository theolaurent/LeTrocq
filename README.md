# LeTrocq

[![CI](https://github.com/theolaurent/LeTrocq/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/theolaurent/LeTrocq/actions/workflows/ci.yml)
[![Documentation](https://github.com/theolaurent/LeTrocq/actions/workflows/docs.yml/badge.svg?branch=main)](https://github.com/theolaurent/LeTrocq/actions/workflows/docs.yml)

A Lean-native, **graded** reformulation of the [Trocq](https://arxiv.org/abs/2310.14022)
parametricity / proof-transfer framework (Cohen–Crance–Mahboubi), in the **no-univalence**
fragment. Register an equivalence between two types once, and LeTrocq automatically transports
types, terms, and goals across it — generating verified `Param` witnesses whose transport maps
compute.

Two design aims set this port apart. **Library-agnostic:** no dependencies beyond Lean core, and
the driver hardcodes no types — even `List` and the kernel constant `Quot` are ordinary `@[trocq]`
registrations it reads from an environment extension. **Predictable:** transfer is a single deterministic top-down
pass — no typeclass resolution, no backtracking search, no constraint-solving fixpoint — so it either
produces a witness or fails with a definite reason. Every generated proof is choice-free (only
`propext`/`Quot.sound`).

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

## User surface

| Syntax        | Produces                                                        |
|---------------|----------------------------------------------------------------|
| `transfer% T` | the witness `Param (4,4) T T'` (exposes `T'` and its maps)      |
| `trocq`       | transfers the goal `G` to its counterpart `G'`, leaving you `G'`|
| `translate% t`| the counterpart `⟨t⟩` (rebuilt over the target, leaf by leaf)   |
| `relate% t`   | the relatedness `[t] : 〚T〛 t ⟨t⟩`                              |

## Registering your own equivalence

Prove a witness and tag it `@[trocq]`; the driver reads it from the environment. A witness is
classified by its type into a **base** (`Param m n A B`), a **relator** (`∀ …, Param … (F …) (F' …)` — also
how a `Prop` predicate or connective registers, since a proposition is just a `Sort 0` type), a **type
former** (the parametricity relation of a parameterized type), or a **term primitive**. See
`src/Examples/NatUnary.lean` (a base) and `src/LeTrocq/ParamLib/` (prelude types) for the recipes. A ground type
needs no registration at all: a type (or term) whose counterpart is itself is short-circuited to the generic
diagonal `paramRefl` (relation `PLift (a = b)`, identity maps), so `Nat`/`Bool`/`Empty`/`Unit` transfer to
themselves out of the box — and a registered equivalence (e.g. `Nat ≃ Unary`) overrides that whenever it applies.

## How it works

The translation is **twofold**: a counterpart `⟨·⟩` rebuilds a term on the target side, and a graded
relational `[·]` produces the witness that the counterpart is correct (`[t u] = [t] u ⟨u⟩ [u]`).
Neither ever unfolds a definition — both bottom out at `@[trocq]`-registered witnesses.

Grades are **pairs of map-classes** `(m, n)` over the diamond `0 < 1 < {2a,2b} < 3 < 4`, one per
transport direction, recording how much structure a relation carries (bare relation → map → soundness
→ completeness → equivalence). A witness is **registered strong** (usually `(4,4)`) and **used minimal**:
a dedicated solver infers the least class each occurrence needs, and a weakening map bridges the two.
Without univalence the universe is capped at `(2a,2a)`, but concrete types still reach `(4,4)` because a
class-4 relation is forced to be a subsingleton.

See [`DESIGN.md`](DESIGN.md) for the full account.

### Module map

```
Lattice      class algebra: the MapClass/ParamClass diamond, order/join/meet, axiom boundary
Hierarchy    the Param records + weakening (⇓) maps
ParamCC/     graded combinators + their grading tables: Arrow, Forall, Universe
Registry     classify a @[trocq] witness from its type
Attr         the @[trocq] attribute + env extension
TranslateTerm  the counterpart translation ⟨·⟩
Solver       the @[trocq] registries + relator argument-routing (relatorArgKinds)
Transfer     the graded relational translation [·] (demand-driven, single pass)
Tactic       the four user surfaces
ParamLib/    @[trocq] registrations for prelude types
```

## Build

```sh
lake build   # warnings are errors
lake test    # test suite + axiom-footprint guard
```
