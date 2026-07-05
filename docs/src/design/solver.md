# The demand-driven witness solver

The relational translation $\Rel{\cdot}$ is realised as a single syntax-directed pass that
**produces the $\Param$ witness directly**, driven by a demanded output class: no constraint graph, no
least fixpoint. It has two mutually-recursive halves — a top-down *type* judgment and a bottom-up
*term* judgment.

<a id="def-judgments"></a>
**Definition 19 (The three judgments).**

$$
\begin{array}{lll}
  \text{Type check} & \Gamma \vdash T \chk \cls{n}{m} \rw p & p : \Param\;n\;m\;T\;\Cpt{T} \quad(\text{top-down})\\
  \text{Type leaf}  & \Gamma \vdash T \syn \cls{n}{m} \rw p & (\text{atoms / type-vars: read the available class})\\
  \text{Term}       & \Gamma \vdash t \rw r                 & r : \Sem{\mathrm{typeof}\,t}\; t\; \Cpt{t}
\end{array}
$$

A type variable enters the context as
$A \mapsto (\Cpt{A} = A',\ a_R : \Param\;4\;4\;A\;A')$ (pinned strong); a term variable as
$x \mapsto (x',\ x_R : \Sem{T}\,x\,x')$. Both halves share one environment (`SEnv`); a type variable's
`fvar` has a $\SortU$ type, a term variable's does not, so the two never confuse the judgments.

<a id="def-subsumption"></a>
**Definition 20 (Subsumption — the only mode switch).**

$$
\irule{ \Gamma \vdash T \syn \cls{n'}{m'} \rw p \qquad \cls{n}{m} \leq \cls{n'}{m'} }
      { \Gamma \vdash T \chk \cls{n}{m} \rw \mathrm{weaken}\;p }
$$

Used to satisfy a check demand from a leaf's inferred available class.

## The type judgment (check, top-down)

<a id="def-assemble"></a>
**Definition 21 (The type check pass).**
$\texttt{assemble} : \mathsf{Expr} \to \mathsf{ParamClass} \to \mathsf{MetaM}\,\mathsf{Expr}$ walks a
type top-down, building its $\Param$ witness directly at the demanded class. The structural rules push
the demand through the variance tables to the minimal part classes and build each node with its
combinator:

$$
\irule{\ }{ \Gamma \vdash \PropSort \chk \cls{n}{m} \rw \texttt{paramPropAt}\;n\;m }
\qquad
\irule{ \cls{n}{m} \leq \cls{2a}{2a} }
      { \Gamma \vdash \Type_w \chk \cls{n}{m} \rw \texttt{paramTypeAtInner}\;n\;m\;4\;4 }
$$

$$
\irule{ \Gamma \vdash A \chk \texttt{arrowVariance}\,\cls{n}{m}.1 \rw p_a \qquad
        \Gamma \vdash B \chk \texttt{arrowVariance}\,\cls{n}{m}.2 \rw p_b }
      { \Gamma \vdash A \to B \chk \cls{n}{m} \rw \texttt{paramArrow}\;n\;m\;p_a\;p_b }
$$

$$
\irule{ \Gamma \vdash D \chk \texttt{forallVariance}\,\cls{n}{m}.1 \rw p_D \qquad
        \Gamma, x{:}D \vdash B \chk \texttt{forallVariance}\,\cls{n}{m}.2 \rw p_b }
      { \Gamma \vdash \Pi x{:}D.\,B \chk \cls{n}{m} \rw \texttt{paramForall}\;n\;m\;p_D\;(\lambda x\,x'\,x_R.\,p_b) }
$$

where a $\Pi$ over a *type* domain ($D = \Type_w$) offers $x$ at inner class $\cls{4}{4}$ and a $\Pi$
over a *term* domain reads the two sides off $p_D$'s type. A leaf — a registered atom, or a bound type
variable offered at $\cls{4}{4}$ — reads its available class and weakens
([Definition 20](#def-subsumption)). A demand $\Type \chk \cls{n}{m}$ with
$\cls{n}{m} \not\leq \cls{2a}{2a}$ **fails**: that is exactly "needs univalence".
*(Lean: `LeTrocq.Transfer.assemble`.)*

<a id="def-inner-class"></a>
**Definition 22 (The inner class is pinned).** Every universe combinator carries its bound type
variable at inner class $\cls{4}{4}$: the top, independent of the capped outer class, weakening to
satisfy every use. Pinning it is what lets a bound variable have a fixed class — no fixpoint — and it
is axiom-free ($\texttt{paramIdAt}\;\cls{4}{4}$ is `paramRefl` weakened).
*(Lean: `LeTrocq.Transfer.innerClass`.)*

<a id="def-mk-univ"></a>
**Definition 23 (The universe cap, enforced).** $\texttt{mkUniv}$ emits the universe combinator at the
demanded outer class, **failing** when it exceeds $\cls{2a}{2a}$. This is where feasibility of a
$\Type$ transfer is decided; there is no separate sort table. *(Lean: `LeTrocq.Transfer.mkUniv`.)*

<a id="def-arg-kind"></a>
**Definition 24 (Relator argument routing).** For an application $F\,a_1\ldots a_k$ of a registered
relator, the abstraction theorem $\Rel{F\,\bar a} = \Rel{F}\,a_1\Cpt{a_1}\Rel{a_1}\ldots$ (then weaken
to the demand) consumes each argument by its *kind*, read off the relator's type by the shape of each
triple's relatedness: `.type` (a $\Param$: a type argument, assembled at the relator's declared class),
`.family` (relatedness telescopes to a $\Param$: a dependent type family, built like a $\Pi$ codomain),
or `.term` (a bare relation: routed to the term judgment). A family reads its domain off its own binder
type, so it need not sit adjacent to that domain. *(Lean: `LeTrocq.Solver.relatorArgKinds`.)*

## The term judgment (abstraction theorem, bottom-up)

<a id="def-assemble-term"></a>
**Definition 25 (The term pass).** $\texttt{assembleTerm}$ is the abstraction theorem, bottoming at
registered term primitives:

$$
\irule{ x \mapsto (\_, x_R) \in \Gamma }{ \Gamma \vdash x \rw x_R }
\qquad
\irule{ c\ \text{a registered primitive} \rw w }{ \Gamma \vdash c \rw w }
$$

$$
\irule{ \Gamma \vdash u \rw u_R \qquad \Gamma \vdash v \rw v_R }
      { \Gamma \vdash u\,v \rw u_R\; v\; \Cpt{v}\; v_R }
$$

$$
\irule{ \Gamma \vdash A \chk \cls{0}{0} \rw p_A \quad (\Sem{A} = p_A.R) \qquad \Gamma, x{:}A \vdash t \rw t_R }
      { \Gamma \vdash \lambda x{:}A.\,t \rw \lambda x\,x'\,x_R.\,t_R }
$$

$$
\irule{ t : \PropSort \qquad \Gamma \vdash t \chk \cls{1}{1} \rw p }
      { \Gamma \vdash t \rw \mathsf{PLift.up}\,(\texttt{iffOfParam}\;p) }
\qquad
\irule{ \text{numeral } n }{ \Gamma \vdash n \rw (\text{expand to succ/zero}) }
$$

A term position consumes only $\Sem{A} = p_A.R$, which is grade-invariant, so the $\lambda$ rule checks
its domain at the cheapest class $\cls{0}{0}$. A proposition is just a $\SortU\,0$ type, so it has no
separate arm: its relatedness $\mathsf{PLift}\,(P \leftrightarrow P')$ is the $\cls{1}{1}$ witness the
relator path builds, projected via `iffOfParam`. *(Lean: `LeTrocq.Transfer.assembleTerm`.)*

## Feasibility and entry points

<a id="rem-feasibility"></a>
**Remark 26 (Feasibility falls out).** A transfer is impossible exactly when a check gets stuck: a
$\Type$ demand above $\cls{2a}{2a}$ ([Definition 23](#def-mk-univ)), or a leaf whose available class
cannot weaken to the demand. Both surface as ordinary rule failures, so there is no separate
feasibility pass.

<a id="def-entry"></a>
**Definition 27 (The entry points).** `transfer` assembles $\Rel{T}$ directly at a root class in one
pass (driving `transfer%` at $\cls{4}{4}$ and the `trocq` tactic at the comap class $\cls{0}{1}$, which
refines the goal by the backward map); `relate` runs the term judgment (driving `relate%`).
`translate%` is $\Cpt{\cdot}$ ([Definition 18](translation.md#def-translate-term)), unchanged.
*(Lean: `LeTrocq.Transfer.transfer`, `LeTrocq.Transfer.relate`.)*

## Map to the code

Where the notation of these two chapters lives in the source (all under `src/LeTrocq/`):

| Notation / concept | Lean declaration | File |
|---|---|---|
| ⟨·⟩ — the counterpart translation | `LeTrocq.Translate.term` | `TranslateTerm.lean` |
| [·] on a type — the graded witness | `LeTrocq.Transfer.assemble` | `Transfer.lean` |
| [·] on a term — the abstraction theorem | `LeTrocq.Transfer.assembleTerm` | `Transfer.lean` |
| 〚·〛 := [·].R — the carried relation | `LeTrocq.Transfer.assembleRel` | `Transfer.lean` |
| `Param` + the class diamond | `LeTrocq.Param` / `LeTrocq.MapClass` | `Hierarchy.lean`, `Lattice.lean` |
| grading (demand → part classes) | inline in `assemble`, via the variance tables | `Transfer.lean`, `ParamCC/` |
| `@[trocq]` registries | `Solver.buildAtomPairs` / `buildConsts` / `relatorArgKinds` | `Solver.lean` |
| the four surfaces | `transfer%` / `trocq` / `translate%` / `relate%` | `Tactic.lean` |
