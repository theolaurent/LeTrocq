/-
The map/comap-carrying COMBINATORS — one construction per file under `LeTrocq/Core/`:

  • `LeTrocq.Core.Arrow`    — `RArrow`, the graded `paramArrow` (+ samples `paramArrowLow`/`paramArrow33`).
  • `LeTrocq.Core.Forall`   — `RForall`, the graded dependent-Π `paramForall`.
  • `LeTrocq.Core.Universe` — `paramId`, `paramType`, `paramTypeAt` (the universe at ≤ (2a,2a)).
  • `LeTrocq.Core.Quot`     — `QuotRel`, `paramQuotR` (quotients, a primitive type).
  • `LeTrocq.Core.Unit`     — `UnitRel`, `UnitR` (the `PUnit` matcher-dummy primitive).

This module re-exports them all. Each builds a `Param` (or the parametricity relation of a primitive) out
of `Param`s for its parts, at a class governed by the dependency tables in `Lattice`.
-/
import LeTrocq.Core.Arrow
import LeTrocq.Core.Forall
import LeTrocq.Core.Universe
import LeTrocq.Core.Quot
import LeTrocq.Core.Unit
