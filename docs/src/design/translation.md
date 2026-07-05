# The graded parametricity translation

LeTrocq is a Lean-native, *graded* reformulation of the parametricity / proof-transfer translation of
Trocq (Cohen–Crance–Mahboubi), in the *no-univalence* fragment. The translation is **twofold**: a
counterpart translation $\Cpt{\cdot}$ and a relational translation $\Rel{\cdot}$, tied by the
abstraction theorem

$$
  t : A \quad\Longrightarrow\quad \Rel{t} : \Sem{A}\, t\, \Cpt{t},
  \qquad\text{where } \Sem{A} := \Rel{A}.R .
$$

$\Cpt{t}$ rebuilds $t$ on the target side; $\Rel{t}$ witnesses that $\Cpt{t}$ really is the
counterpart. Neither ever unfolds a definition — both bottom out at `@[trocq]`-registered witnesses
([Leaves: registered witnesses](#leaves-registered-witnesses)).

## The classical (ungraded) translation

Ignoring grading, on the Calculus of Constructions the two translations are the standard binary
parametricity translation.

<a id="def-classical"></a>
**Definition 1 (The ungraded translation).** The counterpart $\Cpt{\cdot}$ and relation $\Rel{\cdot}$
are defined by mutual structural recursion:

$$
\begin{array}{llcll}
  \Cpt{x}          &= x'                 &\qquad& \Rel{x}         &= x_R \\
  \Cpt{t\,u}       &= \Cpt{t}\,\Cpt{u}   &&      \Rel{t\,u}      &= \Rel{t}\; u\; \Cpt{u}\; \Rel{u} \\
  \Cpt{\lambda x{:}A.\,t} &= \lambda x'{:}\Cpt{A}.\,\Cpt{t} && \Rel{\lambda x{:}A.\,t} &= \lambda x\,x'\,x_R.\,\Rel{t} \\
  \Cpt{\Pi x{:}A.\,B}     &= \Pi x'{:}\Cpt{A}.\,\Cpt{B}     && \Rel{\Pi x{:}A.\,B} &= \Pi x\,x'\,x_R.\,\Rel{B} \\
  \Cpt{\square}    &= \square            &&      \Rel{\square}   &= \square \to \square \to \square
\end{array}
$$

The application clause $\Rel{t\,u} = \Rel{t}\,u\,\Cpt{u}\,\Rel{u}$ is the *abstraction theorem*, and
drives every structural case below. Here $\Rel{A}$ is a bare relation $A \to \Cpt{A} \to \square$; the
grading of [The graded hierarchy](#the-graded-hierarchy) refines it into a record.

## The graded hierarchy

To carry transport *maps* (not just a relation), $\Rel{\cdot}$ on a type returns a record — a witness
of [Definition 5](#def-param) — rather than a bare relation.

<a id="def-map-class"></a>
**Definition 2 (The map-class diamond).** $\MapClass$ is the finite order
$0 < 1 < \{2a, 2b\} < 3 < 4$, with a decidable order `le`, a join and a meet. Semantically a class
records how much structure a relation carries: bare relation ($0$), a forward map ($1$), soundness
`map_in_R` ($2a$), completeness `R_in_map` ($2b$), both ($3$), and their mutual-inverse coherence
($4$). *(Lean: `LeTrocq.MapClass`.)*

<a id="def-param-class"></a>
**Definition 3 (Parametricity classes).** A `ParamClass` is a *pair* $\cls{m}{n}$ of map-classes, one
per transport direction, with pointwise order/join/meet, a direction swap `negate`, and a predicate
`requiresAxiom` that holds iff some component is $\geq 2b$ (i.e. the class needs univalence on a sort
or funext on a $\Pi$). *(Lean: `LeTrocq.ParamClass`.)*

<a id="def-map-has"></a>
**Definition 4 (The six graded records).** For a relation $R : A \to B \to \Type$, $\MapHas\;c\;R$ is
the structure a relation carries at class $c$, selecting one of the records `Map0Has` … `Map4Has`:
`map` $: A \to B$ (from $1$), `map_in_R` (from $2a$), `R_in_map` (from $2b$), and `R_in_mapK` (the
coherence, at $4$). All six live at the uniform $\SortU$ level $\max(u, v{+}1)$, so a $\PropSort$
object fits with no `ULift`. *(Lean: `LeTrocq.MapHas`.)*

<a id="def-param"></a>
**Definition 5 (The witness record).** $\Param\;m\;n\;A\;B$ bundles a relation
$R : A \to B \to \Type$ with $\texttt{cov} : \MapHas\;m\;R$ (forward structure) and
$\texttt{contra} : \MapHas\;n\;(\mathrm{flip}\;R)$ (backward structure). Thus $\cls{4}{4}$ is a full
type equivalence, $\cls{1}{0}$ a forward function, $\cls{0}{1}$ a backward one, $\cls{0}{0}$ a bare
relation. Symmetry (`Param.sym`) swaps `cov`/`contra` onto the reversed relation.
*(Lean: `LeTrocq.Param`.)*

<a id="lem-map4-subsingleton"></a>
**Lemma 6 (Class-4 relations are subsingletons).** If $R$ carries `Map4Has` data, then $R\,a\,b$ is a
subsingleton for all $a, b$. *(Lean: `LeTrocq.Map4Has.subsingleton`.)*

*Proof.* Two inhabitants of $R\,a\,b$ both map, via `R_in_map`, to proofs of $\texttt{map}\,a = b$,
which are equal by Lean's proof irrelevance; the coherence `R_in_mapK` then forces the two inhabitants
equal. This is exactly "no univalence $\Rightarrow$ class $4$ $=$ class $3$ on h-props", and it makes
the $\cls{4}{4}$ coherence *free* on any relation reachable from class-4 data. $\square$

<a id="def-weaken"></a>
**Definition 7 (Weakening).** The diamond is generated from six covering-edge forgets
($4 \to 3 \to 2a \to 1 \to 0$ and $3 \to 2b \to 1$), each a bare record projection. Composing them,
$\texttt{MapClass.weaken}\;s\;t$ maps $\MapHas\;s\;R \to \MapHas\;t\;R$ whenever $t \leq s$
(impossible cases discharged by `nomatch`); `Param.weaken` lifts this componentwise to
$\Param\;s_m\;s_n \to \Param\;t_m\;t_n$. This is the bridge of the "register strong, use minimal"
discipline ([Grading](#sec-grading)). *(Lean: `LeTrocq.Param.weaken`.)*

## The relation and the universe crux

<a id="def-sem"></a>
**Definition 8 (The carried relation).** $\Sem{A} := \Rel{A}.R$: the relation projected off the graded
witness the translation builds for a type. It is all a term position ever consumes of a type, and it
is grade-invariant.

The universe clause is the crux. On a type, $\Rel{\cdot}$ returns a record, and the relation carried
by the universe is $\Param$ *itself*: $\Sem{\square} = \lambda A\,A'.\;\Param\;\cls{p}{q}\;A\;A'$, so
$\Rel{A} : \Sem{\square}\,A\,\Cpt{A} = \Param\;\cls{p}{q}\;A\;\Cpt{A}$ — the type witness $\Rel{A}$ is
literally an element of the universe's own relation, one level up. The inner class $\cls{p}{q}$ records
how strongly the bound type variable is related; it is *independent* of the (capped) outer class.

<a id="def-param-refl"></a>
**Definition 9 (The reflexive witness).** $\texttt{paramRefl}\;A : \Param\;\cls{4}{4}\;A\;A$ with
relation $R\,a\,b := \mathsf{PLift}\,(a = b)$: the identity map is an equivalence, so all four fields
hold (coherence by `Eq` casing). Weakening it gives $\texttt{paramIdAt}\;p\;q$ at any class,
choice-free. *(Lean: `LeTrocq.paramRefl`.)*

<a id="thm-param-type"></a>
**Theorem 10 (The universe combinator, capped at $\cls{2a}{2a}$).**
$\texttt{paramTypeInner}\;p\;q : \Param\;\cls{2a}{2a}\;\Type_w\;\Type_w$ has relation
$\lambda A\,A'.\;\Param\;\cls{p}{q}\;A\;A'$, with `map_in_R` the $\texttt{Eq.rec}$ of
$\texttt{paramIdAt}\;p\;q$. It cannot climb above $\cls{2a}{2a}$: the completeness field would demand
*univalence*. The inner class $\cls{p}{q}$ is free and independent of the cap.
$\texttt{paramTypeAtInner}\;m\;n\;p\;q$ weakens it to any outer class $\leq \cls{2a}{2a}$.
*(Lean: `LeTrocq.paramTypeAtInner`.)*

<a id="thm-param-prop"></a>
**Theorem 11 (The $\PropSort$ universe, at $\cls{4}{4}$).**
$\texttt{paramProp} : \Param\;\cls{4}{4}\;\PropSort\;\PropSort$ with relation
$\lambda P\,P'.\;\mathsf{PLift}\,(P \leftrightarrow P')$. Unlike $\Type$, it reaches the full
equivalence: `map_in_R` is $\texttt{Eq.rec}$, completeness `R_in_map` is **`propext`**, and the
coherence is free by proof irrelevance (the relation is a subsingleton).
*(Lean: `LeTrocq.paramProp`.)*

<a id="def-param-of-iff"></a>
**Definition 12 (Propositions relate by equivalence).**
$\texttt{paramOfIff} : (P \leftrightarrow P') \to \Param\;\cls{4}{4}\;P\;P'$ carries the equivalence as
its relation $\mathsf{PLift}\,(P \leftrightarrow P')$; completeness is proof irrelevance, so it needs
no axiom beyond the given `iff`. Its inverse on maps is `iffOfParam`. This is the shared builder every
$\PropSort$-valued relator (`Eq`, the connectives) hands its result to.
*(Lean: `LeTrocq.paramOfIff`.)*

## The structural combinators

Each combinator builds a $\Param$ for a former out of $\Param$s for its parts, at any output class,
with the parts at the class a grading table dictates ([Grading](#sec-grading)).

<a id="def-arrow-variance"></a>
**Definition 13 (The arrow relation and its grading table).**
$\RArrow\;R_A\;R_B\;f\;f' := \forall a\,a'.\,R_A\,a\,a' \to R_B\,(f a)\,(f' a')$ is the respectful
relation. $\texttt{arrowVariance}\;c$ returns the minimal (domain, codomain) classes needed to build
the arrow at output class $c$, computed from the per-map-class table `mapArrowVariance` (verbatim from
Trocq's `class.elpi`) as $\mathrm{join}$ of the cov requirement with the negated contra one.
*(Lean: `LeTrocq.arrowVariance`.)*

<a id="thm-param-arrow"></a>
**Theorem 14 (The graded arrow).** $\texttt{paramArrow}\;m\;n$ builds
$\Param\;\cls{m}{n}\;(A \to B)\;(A' \to B')$ from parts at the `arrowVariance`-minimal classes, for
*every* output class including $\cls{4}{4}$. The forward map is
$B.\mathrm{fwd} \circ f \circ A.\mathrm{bwd}$; completeness in each direction is a `funext` of the
parts' completeness; the $\cls{4}{4}$ coherence is free because class-4 parts have subsingleton
relations ([Lemma 6](#lem-map4-subsingleton)), so the arrow relation is a subsingleton.
*(Lean: `LeTrocq.paramArrow`.)*

<a id="def-forall-variance"></a>
**Definition 15 (The dependent $\Pi$ relation and its grading table).** With a codomain family
$B : A \to \SortU$ and an indexed relation
$R_B : \forall a\,a'.\,R_A\,a\,a' \to B\,a \to B'\,a' \to \Type$, the $\Pi$-relation is
$\RForall\;R_A\;R_B\;f\;f' := \forall a\,a'\,(r : R_A\,a\,a').\,R_B\,a\,a'\,r\,(f a)\,(f' a')$.
$\texttt{forallVariance}$ is the analogue of `arrowVariance`; its wrinkle is that at cov $\geq 2a$ the
domain is needed at the full equivalence (`map4`), so the forward map can produce the relatedness
proof the codomain fiber is indexed by. *(Lean: `LeTrocq.forallVariance`.)*

<a id="thm-param-forall"></a>
**Theorem 16 (The graded dependent $\Pi$).** $\texttt{paramForall}\;m\;n$ builds
$\Param\;\cls{m}{n}\;(\forall a, B\,a)\;(\forall a', B'\,a')$ from a domain witness and a codomain
*family* of witnesses, each at the `forallVariance`-minimal class. Over $\SortU$ (so $B$ may land in
$\PropSort$), whence $\forall x, P\,x$ for a $\PropSort$-valued $P$ transfers. `R_in_map` uses the
domain's completeness to `subst` the fiber and [Lemma 6](#lem-map4-subsingleton) to identify the two
relatedness proofs. *(Lean: `LeTrocq.paramForall`.)*

<a id="sec-grading"></a>
## Grading: register strong, use minimal

A witness is registered once at a **strong** class (typically the equivalence $\cls{4}{4}$); each
occurrence is used at the **minimal** class it needs; a weakening map ([Definition 7](#def-weaken))
bridges the two. The minimal classes are computed **top-down in a single pass**: the demanded output
class flows down through the type's dependency structure, and each former's grading table
([Definition 13](#def-arrow-variance), [Definition 15](#def-forall-variance)) dictates the class each
part is built at — no constraint graph, no fixpoint ([the solver chapter](solver.md)). A leaf is built
at its available class and *weakened* to the demand. One exception: a *bound type variable* is pinned
at $\cls{4}{4}$ (the universe's inner class, [Theorem 10](#thm-param-type)) rather than the join of its
uses — the top weakens to satisfy every use, and pinning it is exactly what removes the fixpoint.

## Leaves: registered witnesses

The structural rules bottom out at `@[trocq]`-registered constants; the translation never unfolds a
definition (an unregistered, non-diagonal head is an error).

<a id="def-reg-kind"></a>
**Definition 17 (Witness classification).** Tagging a constant `@[trocq]` runs `parseEntry`, which
reads the conclusion of its telescoped type into a `RegKind`: a **base**
($\Param\;m\;n\;A\;B$, closed $A,B$), a **relator**
($\forall \ldots, \Param\;m\;n\;(P\ldots)\,(P'\ldots)$ — also how a $\PropSort$ predicate or connective
registers), a **type former** (a parametricity relation, conclusion a $\SortU$), or a **term
primitive** (bare-relation conclusion). Witnesses are stored by name and re-created with fresh universe
levels, so universe-polymorphic witnesses register correctly. *(Lean: `LeTrocq.parseEntry`.)*

<a id="def-translate-term"></a>
**Definition 18 (The counterpart translation).** $\Cpt{\cdot}$ (`Translate.term`) rebuilds a term's
$B$-side counterpart leaf by leaf: a registered head maps to its counterpart, a bound variable to $x'$,
application/$\lambda$/$\Pi$/sort structurally, and a `Nat` numeral through its `succ`/`zero` normal
form. It is the companion to $\Rel{\cdot}$ ($\Rel{t\,u} = \Rel{t}\,u\,\Cpt{u}\,\Rel{u}$).
*(Lean: `LeTrocq.Translate.term`.)*

A parameterized type former $F$ crosses through its relator by the very same abstraction theorem, with
$\Rel{F}$ a $\Param$-valued witness and a final weakening:

$$
  \Rel{F\,a_1 \ldots a_n} := \big(\Rel{F}\; a_1\,\Cpt{a_1}\,\Rel{a_1}\; \ldots\; a_n\,\Cpt{a_n}\,\Rel{a_n}\big)\ \text{weakened to the demand}.
$$
