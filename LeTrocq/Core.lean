/-
The map/comap-carrying COMBINATORS — one construction per file under `LeTrocq/Core/`:

  • `LeTrocq.Core.Arrow`    — `RArrow`, the graded `paramArrow` (+ samples `paramArrowLow`/`paramArrow33`).
  • `LeTrocq.Core.Forall`   — `RForall`, the graded dependent-Π `paramForall`.
  • `LeTrocq.Core.Universe` — `paramId`, `paramType`, `paramTypeAt` (the universe at ≤ (2a,2a)).

This module re-exports them all. Each builds a `Param` out of `Param`s for its parts, at a class governed by
the dependency tables in `Lattice`. (Parameterized prelude types like `List`/`Quot`/`PUnit` are not here —
they are ordinary `@[trocq]` registrations under `LeTrocq/Std/`.)
-/
import LeTrocq.Core.Arrow
import LeTrocq.Core.Forall
import LeTrocq.Core.Universe
