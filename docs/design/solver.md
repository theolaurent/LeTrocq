
# The demand-driven witness solver


## The "bidirectional" judgments

Two auxiliary maps on `MapClass`, used only in the contravariant *domain* position:
- $\conjugate{\cdot}$ swaps $2a\leftrightarrow 2b$

- $D$ bumps $0\mapsto 0,\ \ 1,2b\mapsto 2a,\ \ 2a,3,4\mapsto 4$ — a $\Pi$ domain needs the full
  equivalence once its codomain transports at $2a$ or above (the wrinkle that separates $\Pi$ from $\to$).

$$
\irule{\ }{\gamma \vdash \PropSort \chk \cls{n}{m}}
\qquad
\irule{n \leq 2a \qquad m \leq 2a}{\gamma \vdash \Type \chk \cls{n}{m}}
\qquad
\irule{\cls{n'}{m'} \in \gamma \qquad \cls{n}{m} \leq \cls{n}{m}}{\gamma \vdash X \chk \cls{n}{m}}
$$

$$
\irule{\gamma \vdash A \chk \cls{\conjugate{m}}{\conjugate{n}} \qquad \gamma \vdash B \chk \cls{n}{m}}
      {\gamma \vdash A \rightarrow B \chk \cls{n}{m}}
\qquad
\irule{\gamma \vdash A \chk \cls{D\,m}{D\,n} \qquad \gamma, x{:}A \vdash B \chk \cls{n}{m}}
      {\gamma \vdash \Prod{A}{B} \chk \cls{n}{m}}
$$

harder to explain

$$
\irule{ \gamma \vdash a_i \chk c_i\ \ (a_i\ \text{a type}) \qquad
        \gamma \vdash a_j \rw \Rel{a_j}\ \ (a_j\ \text{a term}) }
      { \gamma \vdash F\,a_1\cdots a_k \chk \cls{n}{m} }
$$

$$
\irule{\Cpt{T} \equiv T}{\gamma \vdash T \chk \cls{n}{m}}
$$

The leaves and their side-conditions:
- **$X$** — a registered atom, or a bound type variable (pinned at $\cls{4}{4}$): checks against its
  available class $\mathrm{av}(X)$ by weakening.
- **$\Cpt{T} \equiv T$** — a *ground* type, whose counterpart is itself: related by reflexivity at
  every class, with no structural descent (this is why base types need no registration). Excludes a
  bare sort.
- **$F\,a_1\cdots a_k$** — a registered relator, graded and specialized to $\cls{n}{m}$ first, so its
  result already sits at the demand; each argument is routed by *kind*, read off $F$'s type — a
  **type** argument checked at the slot class $c_i$, a **family** argument checked like a $\Pi$-codomain
  under its binder, a **term** argument handed to the term judgment.

$\PropSort$ is uncapped — a $\SortU\,0$ is proof-irrelevant, needing no univalence — whereas $\Type$
is capped at $\cls{2a}{2a}$; that asymmetry *is* the boundary. Codomains keep the demand $\cls{n}{m}$;
domains take the negated demand $\cls{m}{n}$, refined by the former's map ($\conjugate{\cdot}$ for $\to$,
$D$ for $\Pi$). The cap and $D$ interact: a $\Pi$ over a $\Type$ domain whose codomain transports at
cov $\geq 2a$ demands that domain at $\cls{4}{4} \not\leq \cls{2a}{2a}$, and **fails** — exactly where a
transfer "needs univalence". *(Lean: `LeTrocq.Transfer.assemble`, through `arrowVariance` /
`forallVariance` / `relatorArgKinds`.)*


