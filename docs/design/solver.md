# The demand-driven solver

> **DISCLAIMER:** This page was written by an AI assistant and still needs human polishing and proof-reading.

*Source: `LeTrocq/Driver/Transfer.lean` (`assemble` / `assembleTerm`).*

Transfer is one syntax-directed sweep driven by a demanded output class. At each former the demand is
pushed through the [variance formula](combinators.md#the-variance-formula) to the minimal class each part
needs, and the node is built by that former's graded combinator. A leaf reads its available class and
weakens to the demand. There is no constraint graph and no fixpoint; infeasibility is a stuck `assemble` —
a `Type` above the `(2a,2a)` ceiling, or a leaf that cannot weaken.

## Auxiliary maps

Used only in the contravariant domain position: $\conjugate{\cdot}$ swaps `2a ↔ 2b` (the arrow domain),
and $\Dbump$ bumps a `Π` domain to the full equivalence once its codomain transports at `2a` or above
(the [Π-wrinkle](combinators.md#forall)).

| $c$ | `0` | `1` | `2a` | `2b` | `3` | `4` |
|---|---|---|---|---|---|---|
| $\conjugate{c}$ | `0` | `1` | `2b` | `2a` | `3` | `4` |
| $\Dbump\,c$ | `0` | `2a` | `4` | `2a` | `4` | `4` |

## The type judgment

Leaves — `Prop` (uncapped), `Type` (capped `2a`), an atom or bound type variable `X` at its available
class $\av(X)$, and the diagonal short-circuit (a type whose counterpart is itself):

$$
\irule{\ }{\gamma \vdash \PropSort \chk \cls{n}{m}}
\quad
\irule{n \leq 2a \quad m \leq 2a}{\gamma \vdash \Type \chk \cls{n}{m}}
\quad
\irule{\cls{n}{m} \leq \av(X)}{\gamma \vdash X \chk \cls{n}{m}}
\quad
\irule{\Cpt{T} \equiv T}{\gamma \vdash T \chk \cls{n}{m}}
$$

Formers — the codomain keeps the demand, the domain takes the negated demand refined by the former's map:

$$
\irule{\gamma \vdash A \chk \cls{\conjugate{m}}{\conjugate{n}} \quad \gamma \vdash B \chk \cls{n}{m}}
      {\gamma \vdash A \rightarrow B \chk \cls{n}{m}}
\qquad
\irule{\gamma \vdash A \chk \cls{\Dbump\,m}{\Dbump\,n} \quad \gamma, x{:}A \vdash B \chk \cls{n}{m}}
      {\gamma \vdash \Prod{A}{B} \chk \cls{n}{m}}
$$

Applied relator — `F` is graded and specialized to the demand first, so its result already sits there;
each argument is routed by kind (a type argument checked at its slot class $c_i$, a family argument like a
`Π`-codomain, a term argument sent to the term judgment; see [the registry](registry.md)):

$$
\irule{ \gamma \vdash a_i \chk c_i\ \ (a_i\ \text{a type}) \quad
        \gamma \vdash a_j \rw \Rel{a_j}\ \ (a_j\ \text{a term}) }
      { \gamma \vdash F\,a_1\cdots a_k \chk \cls{n}{m} }
$$

The atom/variable leaf covers a registered atom and a bound type variable pinned at `(4,4)`, both checked
by weakening. The diagonal leaf relates a ground type by `paramRefl` at every class with no structural
descent — why base types need no registration — and excludes a bare sort or universe binder, which must
keep their parametric witness.

## The no-fixpoint story

In Trocq a bound type variable's class is the join over all its uses — a constraint-solving fixpoint. Here
every bound variable is pinned at `(4,4)` (the universe combinator's free inner class), and each use
weakens down. Since `(4,4)` weakens to any demand, a variable's class no longer depends on its uses, so
one sweep suffices.

## The cap is the boundary

`Prop` is uncapped (`Sort 0` is proof-irrelevant); `Type` is capped at `(2a,2a)`. A `Π` over a `Type`
domain whose codomain transports at cov `≥ 2a` demands that domain at `(4,4) ≰ (2a,2a)` and fails —
exactly where a transfer "needs univalence".

## The term half

`assembleTerm` is the abstraction theorem `[t u] = [t] u ⟨u⟩ [u]`, bottoming at registered term
primitives. A proposition builds its `(1,1)` `Param` and projects via `iffOfParam` to `PLift (P ↔ P')`;
numerals expand through `succ` / `zero`; a diagonal term gives `PLift.up rfl` (gated on both the type and
the term being diagonal, and excluding polymorphic-typed terms).

## Seeding

`transfer% T` seeds at `(4,4)` (the full equivalence); `trocq` seeds at `(0,1)` — it needs only the
backward map `G' → G` (the contra map at class 1) to refine the goal.
