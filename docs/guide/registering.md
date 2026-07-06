# Registering your own equivalence

> **DISCLAIMER:** This page was written by an AI assistant and still needs human polishing and proof-reading.

Prove a witness and tag it `@[trocq]`; the driver reads it from the environment. Tagging classifies the
witness immediately (`parseEntry`, in `LeTrocq/Driver/Registry.lean`), so a malformed one is rejected at
the tag site. There are four kinds:

| Kind | Type shape | Registers |
|---|---|---|
| **base** | `Param m n A B` (`A`, `B` closed consts) | an equivalence of two types |
| **relator** | `∀ (m n : MapClass) …, Param m n (F …) (F' …)` | an applied head `F` (graded) |
| **type former** | `∀ …, F args → F' args' → Sort` | the parametricity relation of a parameterized type |
| **term primitive** | `∀ …, R … (c …) (c' …)` (`R` a bare relation) | a term head `c ↦ c'` |

A `Prop` predicate or connective is a `Sort 0` type, so it registers as a **relator** — no separate `Prop`
machinery. Full detail: [the registry](../design/registry.md).

## A base equivalence

Define the two types and their conversions, prove the equivalence, and tag the `Param (4,4)` witness at
the strong class. Each use is weakened to its minimal class automatically, and the backward reading
`Unary ≃ Nat` comes free via `Param.sym`.

```lean
def RNU : Nat → Unary → Type := fun n u => PLift (u.toNat = n)

@[trocq] def RN : Param .map4 .map4 Nat Unary where
  R := RNU
  cov := { map := Unary.ofNat, mapInR := …, rInMap := …, rInMapK := fun _ _ _ => rfl }
  contra := { map := Unary.toNat, mapInR := …, rInMap := …, rInMapK := fun _ _ _ => rfl }
```

## Term primitives

Register each operation's relatedness so the term translation can cross it. Binders come in
abstraction-theorem triples `(a, a', aR)`; the conclusion is a bare relation naming the heads `c ↦ c'`.
Registering a recursor primitive (`Nat.rec ↦ Unary.rec`) lets the translation cross recursion.

```lean
@[trocq] def R0 : RNU Nat.zero Unary.z := PLift.up rfl
@[trocq] def Rsucc (n : Nat) (u : Unary) (h : RNU n u) : RNU (Nat.succ n) (Unary.s u) := …
```

## Parameterized types

A type constructor like `List : Type → Type` is a graded relator that builds `List` at any output class,
with the element at the variance-minimal class ([combinators](../design/combinators.md)). It registers on
both surfaces: a **type former** (the inductive relation `ListR`) plus its constructors as **term
primitives** for `⟨·⟩` / `[·]`, and the **graded relator** `paramList` for `trocq` / `transfer%`.

Reference patterns: `LeTrocq/Lib/List.lean`; `Lib/Sigma.lean` and `Lib/Quot.lean` (dependent families, a
`Prop`-relation argument); `Examples/WTree.lean` (a non-prelude dependent W-type).

## Ground types need nothing

A type or term whose counterpart is itself short-circuits to the diagonal witness `paramRefl` (relation
`PLift (a = b)`, identity maps), so `Nat`, `Bool`, `Empty`, `Unit`, and any composite of such parts
transfer with no registration. A registered equivalence overrides the diagonal whenever it applies.
