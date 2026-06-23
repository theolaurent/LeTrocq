/-
Trocq — a Lean-native reformulation of modular parametricity / proof transfer.

Library layers (each builds on the previous):
  • `Trocq.Lattice`     — the class algebra: MapClass/ParamClass lattice, dependency tables, solver.
  • `Trocq.Hierarchy`   — the graded witness records (`Param m n A B`) + the weakening (⇓) maps.
  • `Trocq.Combinators` — sample map/comap-carrying combinators (arrow, universe) + base fixtures.
  • `Trocq.Arrow`       — the arrow combinator at EVERY output class (graded family, stage 1).
  • `Trocq.Forall`      — the dependent-Π combinator (graded family, stage 2; output ≤ (2b,2b)).
  • `Trocq.Solver`      — the driver: walk a type, solve for minimal classes, assemble the witness.

See `STATUS.md` for current progress and `lean-port-design.md` for the design rationale.
-/
import Trocq.Lattice
import Trocq.Hierarchy
import Trocq.Combinators
import Trocq.Arrow
import Trocq.Forall
import Trocq.Solver
