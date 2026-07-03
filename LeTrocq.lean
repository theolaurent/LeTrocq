/-
LeTrocq — a Lean-native reformulation of modular parametricity / proof transfer.

The library, module by module (each builds on the previous):
  • `LeTrocq.Lattice`     — the class algebra: MapClass/ParamClass lattice, dependency tables, solver.
  • `LeTrocq.Hierarchy`   — the graded witness records (`Param m n A B`) + the weakening (⇓) maps.
  • `LeTrocq.ParamCC`     — the graded combinators of the type theory, one construction per file under
                          `ParamCC/` (`Arrow`, `Forall`, `Universe`).
  • `LeTrocq.Registry`    — classify a witness (base / relator / term primitive) from its type.
  • `LeTrocq.Attr`        — the `@[trocq]` attribute + env extension storing the classified witnesses.
  • `LeTrocq.TranslateTerm` — the term translation `⟨·⟩`: rebuild a term's `B`-side counterpart, leaf by leaf
                          (module `LeTrocq.TranslateTerm`, namespace `LeTrocq.Translate`).
  • `LeTrocq.Solver`      — the grading solver: walk a type, solve for minimal classes, hand back the
                          class-annotated `GradedShape` (the grading annotations).
  • `LeTrocq.Transfer`    — the graded relational translation `[·]`: the relatedness witness from the
                          original term + the solver's `GradedShape`, relying on `Translate`'s `⟨·⟩`. Its
                          type half is graded (combinators at the solved class); its term half is the
                          abstraction theorem (`[t u] = [t] u ⟨u⟩ [u]`). ONE relational translation, no
                          separate "native" pass. Drives `relate%` (terms) and `transfer%`/`trocq` (types).
  • `LeTrocq.Tactic`      — the user surface: all four elaborators (`transfer%`/`trocq`/`translate%`/`relate%`).
  • `LeTrocq.ParamLib`    — the parametricity library: `@[trocq]` registrations for prelude types
                          (`Bool`, `Nat`, `List`, `Option`, `Array`, `Prod`, `Sum`, `Sigma`, the empty/unit
                          types `Empty`/`Unit`/`False`/`True`, the kernel constant `Quot`, propositional
                          equality `Eq`, and the logical connectives `Not`/`And`/`Or`/`Iff`), so
                          `import LeTrocq` gives transfer over them out of the box. The ground types
                          (`Bool`/`Nat`/…) register the diagonal, overridable by a user equivalence (e.g.
                          `Nat ≃ Unary`).
-/
import LeTrocq.Lattice
import LeTrocq.Hierarchy
import LeTrocq.ParamCC
import LeTrocq.Registry
import LeTrocq.Attr
import LeTrocq.TranslateTerm
import LeTrocq.Solver
import LeTrocq.Transfer
import LeTrocq.Tactic
import LeTrocq.ParamLib
