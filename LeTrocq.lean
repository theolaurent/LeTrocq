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
  • `LeTrocq.Solver`      — the `@[trocq]` registries the translation reads (`buildAtomPairs`/`buildConsts`) plus
                          `relatorArgKinds` (a relator's per-argument routing). NOT a grading solver anymore —
                          grading is inline in `Transfer` (bidir_solver.md).
  • `LeTrocq.Transfer`    — the graded relational translation `[·]`, a single demand-driven pass: `assemble`
                          walks a type top-down, pushing the demanded class through the dependency tables to the
                          minimal class each part needs and building it with its graded combinator (no constraint
                          graph, no fixpoint). Its term half (`assembleTerm`) is the abstraction theorem
                          (`[t u] = [t] u ⟨u⟩ [u]`). ONE relational translation, no separate "native" pass. Drives
                          `relate%` (terms) and `transfer%`/`trocq` (types).
  • `LeTrocq.Tactic`      — the user surface: all four elaborators (`transfer%`/`trocq`/`translate%`/`relate%`).
  • `LeTrocq.ParamLib`    — the parametricity library: `@[trocq]` registrations for prelude types
                          (`List`, `Option`, `Array`, `Prod`, `Sum`, `Sigma`, the kernel constant `Quot`,
                          propositional equality `Eq`, and the logical connectives `Not`/`And`/`Or`/`Iff`), so
                          `import LeTrocq` gives transfer over them out of the box. Ground types (`Bool`, `Nat`,
                          `Empty`, `Unit`, `True`, `False`) need NO registration — a type/term whose counterpart
                          is itself is short-circuited to the generic diagonal `paramRefl` in `Transfer` — and a
                          user equivalence (e.g. `Nat ≃ Unary`) overrides that diagonal whenever it applies.
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
