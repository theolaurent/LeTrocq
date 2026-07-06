# The parametricity translation

> **DISCLAIMER:** This page was written by an AI assistant and still needs human polishing and proof-reading.

*Source: `LeTrocq/Driver/Counterpart.lean` (`⟨·⟩`) and `LeTrocq/Driver/Transfer.lean` (`[·]`).*

Transfer rests on a binary parametricity translation with three ingredients: the counterpart `⟨t⟩`
(rebuild `t` over `B`), the relation `〚A〛 = [A].R`, and the witness `[t] : 〚T〛 t ⟨t⟩`.

## The classical (ungraded) translation

Ignoring grading, on the Calculus of Constructions this is the standard binary translation:

$$
\begin{array}{llcll}
  \Cpt{x}          &= x'                 &\qquad& \Rel{x}         &= x_R \\
  \Cpt{t\,u}       &= \Cpt{t}\,\Cpt{u}   &&      \Rel{t\,u}      &= \Rel{t}\; u\; \Cpt{u}\; \Rel{u} \\
  \Cpt{\lambda x{:}A.\,t} &= \lambda x'{:}\Cpt{A}.\,\Cpt{t} && \Rel{\lambda x{:}A.\,t} &= \lambda x\,x'\,x_R.\,\Rel{t} \\
  \Cpt{\Pi x{:}A.\,B}     &= \Pi x'{:}\Cpt{A}.\,\Cpt{B}     && \Rel{\Pi x{:}A.\,B} &= \Pi x\,x'\,x_R.\,\Rel{B} \\
  \Cpt{\square}    &= \square            &&      \Rel{\square}   &= \square \to \square \to \square
\end{array}
$$

Grading refines the uniform universe relation `⟦□⟧ = □ → □ → □`: LeTrocq's is `Param`-valued and capped
([combinators](combinators.md#universe--prop)).

## The counterpart `⟨·⟩`

`⟨t⟩` is `t` rebuilt leaf-by-leaf over `B`, bottoming at registered primitives; an unregistered head is
its own counterpart (the diagonal) or an error. It never unfolds.

$$
\begin{array}{lll}
  \Cpt{c} = c' & \Cpt{x} = x' & \Cpt{t\,u} = \Cpt{t}\,\Cpt{u} \\
  \Cpt{\lambda x{:}A.\,b} = \lambda x'{:}\Cpt{A}.\,\Cpt{b} &
  \Cpt{\Pi x{:}A.\,B} = \Pi x'{:}\Cpt{A}.\,\Cpt{B} &
  \Cpt{\SortU} = \SortU
\end{array}
$$

Numerals expand through `succ` / `zero`.

## The relatedness `[·]`

The term half is the abstraction theorem $\Rel{t\,u} = \Rel{t}\; u\; \Cpt{u}\; \Rel{u}$, bottoming at
registered term primitives. A term position consumes only `〚A〛 = [A].R`, which is grade-invariant, so a
type embedded in a term is built at the cheapest class `(0,0)`. The type half — producing a `Param` at a
demanded class — is [the solver](solver.md).

A proposition is a `Sort 0` type: `[P] : PLift (P ↔ P')` is the type witness projected by `iffOfParam`, so
there is no separate `Prop` arm in either half.

Type-directed selection: an optional demanded target selects registered heads and is destructured down an
application spine, driving `transfer% … to …`.
