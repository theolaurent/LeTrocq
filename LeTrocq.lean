/-
LeTrocq — a Lean-native reformulation of modular parametricity / proof transfer.

The library, module by module (each builds on the previous):
  • `LeTrocq.Lattice`     — the class algebra: MapClass/ParamClass lattice, dependency tables, solver.
  • `LeTrocq.Hierarchy`   — the graded witness records (`Param m n A B`) + the weakening (⇓) maps.
  • `LeTrocq.Core`        — the graded combinators, one construction per file under `Core/`
                          (`Arrow`, `Forall`, `Universe`, `Quot`).
  • `LeTrocq.Registry`    — classify a witness (base / relator / term primitive) from its type.
  • `LeTrocq.Attr`        — the `@[trocq]` attribute + env extension storing the classified witnesses.
  • `LeTrocq.Translate`   — the native parametricity translation: `translate% t` rebuilds a term over `B`.
  • `LeTrocq.Solver`      — the driver: walk a type, solve for minimal classes, assemble the witness.
  • `LeTrocq.Tactic`      — the user surface: all four elaborators (`transfer%`/`trocq`/`translate%`/`relate%`).
  • `LeTrocq.Std`         — the standard library: `@[trocq]` registrations for prelude parameterized types
                           (`List`, `Option`, `Sigma`), so `import LeTrocq` gives transfer over them out of the box.
-/
import LeTrocq.Lattice
import LeTrocq.Hierarchy
import LeTrocq.Core
import LeTrocq.Registry
import LeTrocq.Attr
import LeTrocq.Translate
import LeTrocq.Solver
import LeTrocq.Tactic
import LeTrocq.Std
