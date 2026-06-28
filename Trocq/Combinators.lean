/-
The map/comap-carrying COMBINATORS — one construction per file under `Trocq/Combinators/`:

  • `Trocq.Combinators.Arrow`    — `RArrow`, the graded `paramArrow` (+ samples `paramArrowLow`/`paramArrow33`).
  • `Trocq.Combinators.Forall`   — `RForall`, the graded dependent-Π `paramForall`.
  • `Trocq.Combinators.Universe` — `paramId`, `paramType`, `paramTypeAt` (the universe at ≤ (2a,2a)).
  • `Trocq.Combinators.Quot`     — `QuotRel`, `paramQuotR` (quotients, a primitive type).

This module re-exports all three. Each builds a `Param` for a composite type former out of `Param`s for
its parts, at a class governed by the dependency tables in `Lattice`.
-/
import Trocq.Combinators.Arrow
import Trocq.Combinators.Forall
import Trocq.Combinators.Universe
import Trocq.Combinators.Quot
