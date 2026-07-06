# The graded relation hierarchy

> **DISCLAIMER:** This page was written by an AI assistant and still needs human polishing and proof-reading.

*Source: `LeTrocq/Core/Class.lean` (the lattice) and `LeTrocq/Core/Param.lean` (the witnesses, weakening).*

## The `MapClass` lattice

A relation `R : A → B → Type` carries increasing structure along the diamond `0 < 1 < {2a,2b} < 3 < 4`:

```
        map4                       join │ 0  1  2a 2b 3  4        meet │ 0  1  2a 2b 3  4
         │                        ──────┼──────────────────      ──────┼──────────────────
        map3                        0   │ 0  1  2a 2b 3  4          0   │ 0  0  0  0  0  0
        ╱  ╲                        1   │ 1  1  2a 2b 3  4          1   │ 0  1  1  1  1  1
     map2a  map2b                   2a  │ 2a 2a 2a 3  3  4          2a  │ 0  1  2a 1  2a 2a
        ╲  ╱                        2b  │ 2b 2b 3  2b 3  4          2b  │ 0  1  1  2b 2b 2b
        map1                        3   │ 3  3  3  3  3  4          3   │ 0  1  2a 2b 3  3
         │                          4   │ 4  4  4  4  4  4          4   │ 0  1  2a 2b 3  4
        map0
```

## `ParamClass`

`ParamClass := MapClass × MapClass` — the annotation pair `(m,n)`, one grade per transport direction.
`le` and `join` are componentwise; `negate (m,n) = (n,m)`; `bot = (0,0)`, `top = (4,4)`.
`requiresAxiom (m,n)` holds iff some component is `≥ 2b` (i.e. needs `propext` / `funext`).

## The six `MapHas` records

`MapHas c R` is the data `R` carries at class `c` (uniform `Sort (max u (v+1))`, so `Prop` fits):

| class | `map` | `mapInR` | `rInMap` | `rInMapK` |
|---|:---:|:---:|:---:|:---:|
| `0`  |     |     |     |     |
| `1`  | ✓ |     |     |     |
| `2a` | ✓ | ✓ |     |     |
| `2b` | ✓ |     | ✓ |     |
| `3`  | ✓ | ✓ | ✓ |     |
| `4`  | ✓ | ✓ | ✓ | ✓ |

- `map : A → B`
- `mapInR : ∀ a b, map a = b → R a b` — soundness (the map's graph is contained in `R`)
- `rInMap : ∀ a b, R a b → map a = b` — completeness (`R` is contained in the map's graph)
- `rInMapK : ∀ a b r, mapInR a b (rInMap a b r) = r` — coherence

`Param m n A B` bundles `R : A → B → Type` with `cov : MapHas m R` and `contra : MapHas n (flip R)`.
`Param.sym : Param m n A B → Param n m B A` swaps `cov`/`contra` and reverses `R`.

## Weakening `⇓`

Six covering-edge forgets, each a record projection:

```
map4 ⟶ map3 ⟶ map2a ⟶ map1 ⟶ map0        forget43 · forget32a · forget2a1 · forget10
             map3 ⟶ map2b ⟶ map1                    forget32b · forget2b1
```

`MapClass.weaken` composes them along the order proof (impossible combinations are `nomatch`);
`Param.weaken` lifts it componentwise. The named downgrades from an equivalence `(4,4)` are
`toRetraction : Param 4 2a`, `toSection : Param 4 2b`, `toFunction : Param 1 0`, and `toRel : Param 0 0`.

## The class-4 subsingleton fact

`Map4Has.subsingleton`: a class-4 relation `R a b` is a subsingleton. `rInMap` lands in an `Eq`, and
proof irrelevance forces its two witnesses equal through `rInMapK`. Consequently the `(4,4)` coherence is
free on any relation reachable from class-4 data — used throughout the combinators (`RArrow.allEq`,
`ListR.allEq`, …).

## The univalence boundary

| universe | ceiling | `mapInR` | `rInMap` (completeness) | `rInMapK` |
|---|---|---|---|---|
| `Prop` (`Sort 0`) | `(4,4)` | `Eq.rec` | **`propext`** | free (proof irrelevance) |
| `Type w` (`Sort (w+1)`) | `(2a,2a)` | `Eq.rec` | needs **univalence** → blocked | — |

This asymmetry is the "with or without univalence" boundary; `mkUniv` enforces the `Type` cap
structurally.
