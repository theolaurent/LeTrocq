/-
LeTrocq — a Lean-native reformulation of modular parametricity / proof transfer.

The library, module by module (each builds on the previous):
  • `LeTrocq.Lattice`     — the class algebra: MapClass/ParamClass lattice, dependency tables, solver.
  • `LeTrocq.Hierarchy`   — the graded witness records (`Param m n A B`) + the weakening (⇓) maps.
  • `LeTrocq.ParamCC`     — the graded combinators of the type theory, one construction per file under
                          `ParamCC/` (`Arrow`, `Forall`, `Universe`).
  • `LeTrocq.Registry`    — classify a witness (base / relator / term primitive) from its type.
  • `LeTrocq.Attr`        — the `@[trocq]` attribute + env extension storing the classified witnesses.
  • `LeTrocq.Translate`   — the native parametricity translation: `translate% t` rebuilds a term over `B`.
  • `LeTrocq.Solver`      — the driver: walk a type, solve for minimal classes, assemble the witness.
  • `LeTrocq.Tactic`      — the user surface: all four elaborators (`transfer%`/`trocq`/`translate%`/`relate%`).
  • `LeTrocq.ParamLib`    — the parametricity library: `@[trocq]` registrations for prelude types
                          (`List`, `Option`, `Sigma`, and the kernel constants `Quot`/`PUnit`), so
                          `import LeTrocq` gives transfer over them out of the box.
-/
import LeTrocq.Lattice
import LeTrocq.Hierarchy
import LeTrocq.ParamCC
import LeTrocq.Registry
import LeTrocq.Attr
import LeTrocq.Translate
import LeTrocq.Solver
import LeTrocq.Tactic
import LeTrocq.ParamLib
