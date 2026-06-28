/-
Trocq — a Lean-native reformulation of modular parametricity / proof transfer.

The library, module by module (each builds on the previous):
  • `Trocq.Lattice`     — the class algebra: MapClass/ParamClass lattice, dependency tables, solver.
  • `Trocq.Hierarchy`   — the graded witness records (`Param m n A B`) + the weakening (⇓) maps.
  • `Trocq.Combinators` — the graded combinators, one construction per file under `Combinators/`
                           (`Arrow`, `Forall`, `Universe`, `Quot`).
  • `Trocq.Registry`    — classify a witness (base / relator / term primitive) from its type.
  • `Trocq.Attr`        — the `@[trocq]` attribute + env extension storing the classified witnesses.
  • `Trocq.Solver`      — the driver: walk a type, solve for minimal classes, assemble the witness.
  • `Trocq.Tactic`      — the user surface: the `transfer%` term elaborator and the `trocq` tactic.
  • `Trocq.Translate`   — the native parametricity translation: `translate% t` rebuilds a term over `B`.

See `STATUS.md` for current progress and `lean-port-design.md` for the design rationale.
-/
import Trocq.Lattice
import Trocq.Hierarchy
import Trocq.Combinators
import Trocq.Registry
import Trocq.Attr
import Trocq.Solver
import Trocq.Tactic
import Trocq.Translate
