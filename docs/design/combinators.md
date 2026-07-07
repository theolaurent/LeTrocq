# The graded combinators

> **DISCLAIMER:** This page was written by an AI assistant and still needs human polishing and proof-reading.

*Source: `LeTrocq/Combinators/{Universe,Arrow,Forall}.lean` and the relators in `LeTrocq/Lib/*.lean`.*

Each former builds a `Param m n` at any output class from `Param`s for its parts, each part at the
variance-minimal class. Soundness fields (`mapInR`) are shared across the `2a/3/4` arms, completeness
(`rInMap`) across `2b/3/4`, and the `(4,4)` coherence is free by subsingleton-ness
([hierarchy](hierarchy.md#the-class-4-subsingleton-fact)).

## The variance formula

A former with per-map-class primitive table $\mathrm{mv} : \MapClass \to \ParamClass$ inverts a demand
`c` to part classes by

$$ \variance(c) = \mathrm{mv}(c_1) \join \negate\,\mathrm{mv}(c_2). $$

The solver inverts each demand through this; each `param⋆`'s type consumes the result.

## Universe / Prop

| combinator | outer class | relation carried | completeness |
|---|---|---|---|
| `paramRefl` | `(4,4)` | `PLift (a = b)` | `Eq` casing |
| `paramTypeAt m n p q` | `≤ (2a,2a)` | `Param p q A A'` | `Eq.rec` (`mapInR`) only |
| `paramProp` | `(4,4)` | `PLift (P ↔ P')` | `propext` |

`mkUniv` caps `Type` at `(2a,2a)` (throwing above it). The inner class `(p,q)` of `paramTypeAt` is free —
the driver pins it at `(4,4)`, which is what removes the [fixpoint](solver.md#the-no-fixpoint-story).

## Arrow

`RArrow RA RB f f' := ∀ a a', RA a a' → RB (f a) (f' a')` (the respectful relation, = Mathlib `LiftFun`).
`paramArrow m n` builds every class including `(4,4)` (free via `RArrow.allEq` when the codomain part is
`map4`), with parts at `mapArrowVariance` (domain **contra**, codomain **cov**):

| output `m` | domain `(cov,contra)` | codomain `(cov,contra)` |
|---|---|---|
| `0`  | `(0,0)`  | `(0,0)`  |
| `1`  | `(0,1)`  | `(1,0)`  |
| `2a` | `(0,2b)` | `(2a,0)` |
| `2b` | `(0,2a)` | `(2b,0)` |
| `3`  | `(0,3)`  | `(3,0)`  |
| `4`  | `(0,4)`  | `(4,0)`  |

## Forall

`RForall RA RB f f' := ∀ a a' (aRel : RA a a'), RB a a' aRel (f a) (f' a')` — the codomain is a family.

| output `m` | domain `(cov,contra)` | codomain `(cov,contra)` |
|---|---|---|
| `0`  | `(0,0)`  | `(0,0)`  |
| `1`  | `(0,2a)` | `(1,0)`  |
| `2a` | `(0,4)`  | `(2a,0)` |
| `2b` | `(0,2a)` | `(2b,0)` |
| `3`  | `(0,4)`  | `(3,0)`  |
| `4`  | `(0,4)`  | `(4,0)`  |

**The Π-wrinkle:** at cov `≥ 2a` the domain is demanded at `map4` (the `(0,4)` entries). The forward map
must manufacture a domain-relatedness proof — `rInMap` gives `bwd a' = a` to `subst` the fiber, and the
class-4 subsingleton identifies the two proofs. This separates `Π` from `→`, and is the `D` map in
[the solver](solver.md#auxiliary-maps).

## The `Lib` relators

The prelude relators reuse the same shape with their own tables.

**`List`** — covariant, so the element class is the identity: `m ↦ (m,0)`.

**`Sigma`** (domain with the Π-wrinkle, family covariant) and **`WTree`** (same domain, **contravariant**
family — note the `2a↔2b` swap in its family column):

| output `m` | Sigma domain | Sigma family | WTree domain | WTree family |
|---|---|---|---|---|
| `0`  | `(0,0)`  | `(0,0)`  | `(0,0)`  | `(0,0)`  |
| `1`  | `(2a,0)` | `(1,0)`  | `(2a,0)` | `(0,1)`  |
| `2a` | `(2a,0)` | `(2a,0)` | `(2a,0)` | `(0,2b)` |
| `2b` | `(4,0)`  | `(2b,0)` | `(4,0)`  | `(0,2a)` |
| `3`  | `(4,0)`  | `(3,0)`  | `(4,0)`  | `(0,3)`  |
| `4`  | `(4,0)`  | `(4,0)`  | `(4,0)`  | `(0,4)`  |

**`Quot`** — its relation is `Prop`-truncated, so coherence is always free; the map needs `2a` and
completeness forces `3`: `m ↦` `(0,0)` `(2a,0)` `(2a,0)` `(3,0)` `(3,0)` `(3,0)` for `0…4`.

**`Eq`** — graded, capped at `2b` per direction: transporting the equality one way uses only the
underlying type's completeness (`rInMap`) in that direction (`eqFwd`/`eqBwd`), never a full equivalence, so
`m ↦` `(0,0)` `(2b,0)` … for `0`/`≥1` and `eqVariance (m,n)` tops out at `(2b,2b)` (a one-directional demand
like the `trocq` seed `(0,1)` needs only `(0,2b)`); the related objects are propositions, so the witness's
own completeness/coherence are free by proof irrelevance.

**Connectives** — a `Prop` part carries no data above class 1, so `propMapHas` caps it at `meet · map1`:
`And`/`Or` are covariant (`0 ↦ (0,0)`, else `(1,0)`), `Not` is contravariant (that table negated), and
`Iff` uses both directions (`0 ↦ (0,0)`, else `(1,1)`).
