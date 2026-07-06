# The registry and argument routing

> **DISCLAIMER:** This page was written by an AI assistant and still needs human polishing and proof-reading.

*Source: `LeTrocq/Driver/Registry.lean` and `LeTrocq/Driver/Counterpart.lean` (`buildCtx`).*

Tagging `@[trocq]` runs `parseEntry` eagerly (rejecting a malformed witness at the tag site) and stores
the classified entry in the `trocqExt` environment extension. Grading is not here — it is inline in
[the solver](solver.md); the registry only classifies, stores, and looks up.

## The four kinds

Classified by the shape of the telescoped conclusion:

| kind | type shape | registers |
|---|---|---|
| **base** | `Param m n A B` (`A`,`B` closed consts, no binders) | an equivalence of two types |
| **relator** | `∀ (m n : MapClass) …, Param m n (F …) (F' …)` | an applied head `F` (graded) |
| **type former** | `∀ …, F args → F' args' → Sort` | the parametricity relation of a parameterized type |
| **term primitive** | `∀ …, R … (c …) (c' …)` (`R` a bare relation) | a term head `c ↦ c'` |

Every parameterized relator must be graded; only a closed base may be ungraded. A graded relator also
gives `⟨·⟩` the counterpart head `F ↦ F'` (read off its conclusion) — how connectives and `Prop`
predicates, which have no type former, get a counterpart.

## Argument routing

A relator's binders come in abstraction-theorem triples `(a, a', aRel)`; `relatorArgKinds` reads each
argument's kind off the shape of its relatedness slot `aRel`:

| `ArgKind` | shape of `aRel` | how `assemble` consumes it |
|---|---|---|
| `.type (m,n)` | `Param m n A A'` | build the argument's `Param` at the slot class |
| `.family (m,n) domIdx` | `∀ a a' (aRel : RA a a'), Param m n (B a) (B' a')` | build a `Param` family, like a `Π`-codomain |
| `.term` | a bare relation | hand to the term half (`⟨a⟩`, `[a]`) |

`domIdx` is found by matching the family binder's domain to an earlier type-argument binder, so a family
need not be adjacent to its domain (the `Tw` test).

## Bidirectional indexing

`insertBidirPair` installs `srcHead ↦ tgtHead ↦ …` in both directions with a preferred (last-registered)
target per source; a homogeneous head (`List ↦ List`) skips the backward entry. Backward witnesses are a
base's `Param.sym` and a term primitive's `symPrimitive` (swap the value pair in each triple, keep the
relatedness slot). These feed `buildAtomPairs` (bases), `buildConsts` (relators), and `buildCtx` (the
`⟨·⟩` context).
