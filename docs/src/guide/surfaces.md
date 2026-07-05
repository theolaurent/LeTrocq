# The user surfaces

LeTrocq exposes four elaborators/tactics (all in `LeTrocq/Tactic.lean`). They are thin wrappers over
the driver; nothing is tied to a particular base.

| Syntax          | Produces                                                          |
|-----------------|------------------------------------------------------------------|
| `transfer% T`   | the witness `Param (4,4) T T'` (exposes `T'` and its maps)        |
| `trocq`         | transfers the goal `G` to its counterpart `G'`, leaving you `G'`  |
| `translate% t`  | the counterpart `⟨t⟩` (rebuilt over the target, leaf by leaf)     |
| `relate% t`     | the relatedness `[t] : 〚T〛 t ⟨t⟩`                                |

## `transfer% T`

Elaborates to the relatedness witness `Param (4,4) T T'` for a type `T` built over registered bases.
It exposes the generated counterpart `T'` and its transport maps:

```lean
-- the forward transport of `Nat → Nat` is a `(Nat → Nat) → (Unary → Unary)`:
#check (transfer% (Nat → Nat)).cov.map
```

An optional `to T'` **demands** a specific target, disambiguating a source that has several
registered equivalences:

```lean
transfer% Nat to Unary     -- pick the Nat ≃ Unary base explicitly
```

Without `to`, the *preferred* (last-registered) target for the head is used.

## `trocq`

A tactic: it transfers the current goal `G` to its counterpart `G'` (seeded at the comap class
`(0,1)`) and refines `G` by the backward transport `G' → G`, leaving you to prove the (hopefully
easier) `G'`.

```lean
example : Unary → Unary := by
  trocq            -- ⊢ Nat → Nat
  exact (· + 1)
```

`trocq to G'` demands a specific target goal `G'`; the produced counterpart must then match it
(checked by `isDefEq`).

## `translate% t`

Elaborates to the `B`-side counterpart `⟨t⟩` — `t` rebuilt over the target side leaf-by-leaf (**not**
`iso ∘ t ∘ iso⁻¹`). It never unfolds a definition; an unregistered, non-diagonal head is an error.

```lean
-- with `Nat ≃ Unary` registered, the successor function crosses to the `Unary` successor:
#check translate% (fun n : Nat => n + 1)
```

## `relate% t`

Elaborates to the relatedness `[t] : 〚T〛 t ⟨t⟩` — the proof that the counterpart is correct. This is
the term half of the [abstraction theorem](../design/translation.md): `[t u] = [t] u ⟨u⟩ [u]`.

```lean
example : PLift ((2 : Nat) = 2) := relate% (2 : Nat)   -- diagonal Nat: relatedness is reflexivity
```

## The two halves

`translate%` and `relate%` are the two halves of the **twofold translation**: `⟨·⟩` rebuilds a term
on the target side, and the graded relational `[·]` produces the witness that the counterpart is
correct. `transfer%` / `trocq` drive the type half of `[·]`; `relate%` drives its term half. See
[the design chapters](../design/translation.md) for the full account.
