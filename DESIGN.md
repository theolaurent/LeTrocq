# The LeTrocq Parametricity Translation

LeTrocq is a Lean-native, *graded* reformulation of the parametricity / proof-transfer
translation of Trocq (Cohen–Crance–Mahboubi), in the **no-univalence** fragment.

The translation is **twofold**: a counterpart translation `⟨·⟩` and a relational translation
`[·]`, tied by the abstraction theorem

    t : A   ⟹   [t] : 〚A〛 t ⟨t⟩          (where 〚A〛 := [A].R, see §2)

`⟨t⟩` rebuilds `t` on the target side; `[t]` is the witness that `⟨t⟩` really is the counterpart.
Neither unfolds definitions — both bottom out at `@[trocq]`-registered witnesses (§5).

## 1. The classical (ungraded) translation

On the Calculus of Constructions, ignoring grading, the two translations are:

    ⟨x⟩        := x'
    ⟨t u⟩      := ⟨t⟩ ⟨u⟩
    ⟨λx:A. t⟩  := λx':⟨A⟩. ⟨t⟩
    ⟨Πx:A. B⟩  := Πx':⟨A⟩. ⟨B⟩
    ⟨□⟩        := □

    [x]        := xR
    [t u]      := [t] u ⟨u⟩ [u]
    [λx:A. t]  := λx:A x':⟨A⟩ xR:[A]. [t]
    [Πx:A. B]  := Πx:A x':⟨A⟩ xR:[A]. [B]
    [□]        := □ → □ → □

Here `[A]` is a bare relation `A → ⟨A⟩ → □`, and `[t u] = [t] u ⟨u⟩ [u]` is the abstraction
theorem: the relatedness of an application is the head's relatedness applied to the argument, its
counterpart, and its relatedness.

## 2. The graded refinement (what LeTrocq implements)

To carry the transport MAPS (not just a relation), `[·]` on a **type** returns a **record** — a
witness `Param m n A ⟨A⟩` (§3) — rather than a bare relation. The relation is recovered by
projection:

    〚A〛 := [A].R

The term rules are unchanged; the type / sort rules produce records:

    [x]        := xR
    [t u]      := [t] u ⟨u⟩ [u]
    [λx:A. t]  := λx:A x':⟨A⟩ xR:〚A〛. [t]
    [Πx:A. B]  := { R := Πx:A x':⟨A⟩ xR:〚A〛. 〚B〛 ;  cov ; contra }
    [□]        := { R := λ A A'. Param@(p,q) A A' ;  cov ; contra }

The last line is the crux. **The relation carried by the universe is `Param` itself**:
`〚□〛 = λ A A'. Param@(p,q) A A'`, so `[A] : 〚□〛 A ⟨A⟩ = Param@(p,q) A ⟨A⟩` — the type witness
`[A]` is literally an element of the universe's own relation, one level up. `[·]` on a type is
therefore just `[·]` at the next universe, and `〚·〛` is its `.R` projection. The inner class
`(p,q)` records how strongly the bound type variable is related; it is independent of the (capped)
outer class.

## 3. The witness record `Param m n A B`

    structure Param (m n : MapClass) (A B) where
      R      : A → B → Type        -- the relation
      cov    : MapHas m R          -- forward-direction structure, at class m
      contra : MapHas n (flip R)   -- backward-direction structure, at class n

The grade is a **pair** `(m, n)` of map-classes, one per transport direction. A map-class ranges
over the diamond `0 < 1 < {2a, 2b} < 3 < 4`, accumulating fields as it grows:

    0    R only
    1    + map       : A → B
    2a   + map_in_R  : map a = b → R a b      (soundness)
    2b   + R_in_map  : R a b → map a = b      (completeness)
    3    + both map_in_R and R_in_map
    4    + R_in_mapK : soundness and completeness are mutually inverse   (coherence)

So `(4,4)` is a full type equivalence, `(1,0)` a forward function only, `(0,1)` a backward one,
`(0,0)` a bare relation.

**No univalence.** Completeness (`R_in_map`, classes ≥ 2b) needs an axiom — funext for a Π,
univalence for the sort — so the **universe** `[□]` is capped at `(2a, 2a)`: `map_in_R` is `Eq.rec`
(free), but the completeness half is unavailable. Concrete types still reach `(4,4)` without
univalence, because a class-4 relation is forced to be a subsingleton (proof irrelevance makes
`R_in_mapK` free); `Prop` reaches `(4,4)` too — its relation is `P ↔ P'` and completeness is
`propext`.

## 4. Grading: register strong, use minimal

A witness is registered once at a STRONG class (typically the equivalence `(4,4)`); each occurrence
is used at the MINIMAL class it needs; a **weakening** map `Param src → Param tgt` (for `tgt ≤ src`,
forgetting fields) bridges the two.

The minimal classes are computed **top-down in a single pass**: the demanded output class flows down
through the type's dependency structure, and the tables in `Lattice.lean` (`depPi`, `depArrow`,
`depType`) dictate the minimal class each part is built at (no constraint graph, no fixpoint —
`bidir_solver.md`). A leaf (a registered atom, or a bound type variable) is built at its available
class and *weakened* to the demand. One exception to "use minimal": a **bound type variable** is
pinned at `(4,4)` (the universe's inner class, §2) rather than the join of its uses — the top weakens
to satisfy every use, and pinning it is exactly what removes the fixpoint. Grades are written `@(m,n)`.
For a Π at output class `(0,1)`:

    [Πx:A. B]@(0,1) := { R := Πx:A x':⟨A⟩ xR:〚A〛@(2a,0). 〚B〛@(0,1) ;  cov ; contra }

i.e. to transport that Π, the domain relation is needed only at `〚A〛@(2a,0)` and the codomain at
`〚B〛@(0,1)` — exactly what `depPi (0,1)` returns.

## 5. Leaves: registered witnesses, never unfolding

The structural rules bottom out at `@[trocq]`-registered constants; the translation NEVER unfolds a
definition (an unregistered head is an error).

    ⟨c⟩   := registered counterpart   (a term primitive's B-side, a type former's B-head, a Prop predicate's B-side)
    [c]   := registered relatedness   (a term primitive witness, a relator, a Prop primitive)

A parameterized type former `F` crosses through its **relator**:

    [F a₁ … aₙ]@c := ([F] a₁ ⟨a₁⟩ [a₁]  …  aₙ ⟨aₙ⟩ [aₙ]) , weakened to c

which is the very same abstraction theorem `[t u] = [t] u ⟨u⟩ [u]` as for terms, with `[F]` a
`Param`-valued witness (and a final weakening to the solved class). Propositions relate by logical
equivalence: `[P] : PLift (P ↔ P')`.

## Map to the code

    ⟨·⟩    LeTrocq.Translate.term          (TranslateTerm.lean)
    [·]    LeTrocq.Transfer.assemble       (types — graded, builds the records)     (Transfer.lean)
           LeTrocq.Transfer.assembleTerm   (terms — the abstraction theorem; a proposition is a Sort 0
                                            type, so its `PLift (P ↔ P')` is projected off the `Param`)
    〚·〛    LeTrocq.Transfer.assembleRel    (= Param.R ∘ assembleType)
    Param  LeTrocq.Param / MapClass        (the record + the class diamond)         (Hierarchy.lean, Lattice.lean)
    grade  inline in assemble: the demand flows through the dependency tables       (Transfer.lean, Lattice.lean)
    reg    LeTrocq.Solver.buildAtoms/buildConsts/relatorArgKinds (the @[trocq] lookups)  (Solver.lean)

The graded combinators that build each `[·]` node — `paramArrow`, `paramForall`, `paramType` /
`paramProp` — live under `LeTrocq/ParamCC/`. The user surfaces are `transfer%` / `trocq` (types),
`translate%` (`⟨·⟩`), and `relate%` (`[·]`) in `Tactic.lean`.
