# The user surfaces

> **DISCLAIMER:** This page was written by an AI assistant and still needs human polishing and proof-reading.

Four elaborators/tactics, all thin wrappers over the driver (`LeTrocq/Driver/Tactic.lean`); nothing is
tied to a particular base.

| Syntax          | Seeds at | Produces |
|-----------------|----------|----------|
| `transfer% T`   | `(4,4)`  | the witness `Param (4,4) T T'` (exposes `T'` and its maps) |
| `trocq`         | `(0,1)`  | transfers the goal `G` to its counterpart `G'`, leaving you `G'` |
| `translate% t`  | —        | the counterpart `⟨t⟩` (rebuilt over the target, leaf by leaf) |
| `relate% t`     | —        | the relatedness `[t] : 〚T〛 t ⟨t⟩` |

## `transfer% T`

Elaborates to `Param (4,4) T T'`, exposing the counterpart `T'` and its transport maps. An optional
`to T'` demands a specific target (disambiguating a source with several registered equivalences);
otherwise the preferred (last-registered) target is used.

```lean
#check (transfer% (Nat → Nat)).cov.map   -- (Nat → Nat) → (Unary → Unary)
transfer% Nat to Unary
```

## `trocq`

Transfers the current goal to its counterpart and refines it by the backward transport `G' → G` (the
contra map at class 1), leaving the easier `G'`. `trocq to G'` demands a target goal (checked by
`isDefEq`).

```lean
example : Unary → Unary := by
  trocq            -- ⊢ Nat → Nat
  exact (· + 1)
```

## `translate% t` / `relate% t`

`translate%` gives the `B`-side counterpart `⟨t⟩`, rebuilt leaf-by-leaf (not `iso ∘ t ∘ iso⁻¹`); it never
unfolds, and an unregistered non-diagonal head is an error. `relate%` gives the relatedness
`[t] : 〚T〛 t ⟨t⟩` — the term half of the abstraction theorem `[t u] = [t] u ⟨u⟩ [u]`.

```lean
#check translate% (fun n : Nat => n + 1)               -- the Unary successor
example : PLift ((2 : Nat) = 2) := relate% (2 : Nat)   -- diagonal: reflexivity
```

Together they are the twofold translation; `transfer%` / `trocq` drive the type half of `[·]`, `relate%`
its term half. See [the translation](../design/translation.md).
