/-
The map/comap-carrying COMBINATORS — one construction per file under `Trocq/Core/`:

  • `Trocq.Core.Arrow`    — `RArrow`, the graded `paramArrow` (+ samples `paramArrowLow`/`paramArrow33`).
  • `Trocq.Core.Forall`   — `RForall`, the graded dependent-Π `paramForall`.
  • `Trocq.Core.Universe` — `paramId`, `paramType`, `paramTypeAt` (the universe at ≤ (2a,2a)).
  • `Trocq.Core.Quot`     — `QuotRel`, `paramQuotR` (quotients, a primitive type).

This module re-exports all three. Each builds a `Param` for a composite type former out of `Param`s for
its parts, at a class governed by the dependency tables in `Lattice`.
-/
import Trocq.Core.Arrow
import Trocq.Core.Forall
import Trocq.Core.Universe
import Trocq.Core.Quot
