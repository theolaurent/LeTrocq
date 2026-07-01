/-
The map/comap-carrying COMBINATORS — one construction per file under `LeTrocq/ParamCC/`:

  • `LeTrocq.ParamCC.Arrow`    — `RArrow`, the graded `paramArrow` (+ samples `paramArrowLow`/`paramArrow33`).
  • `LeTrocq.ParamCC.Forall`   — `RForall`, the graded dependent-Π `paramForall`.
  • `LeTrocq.ParamCC.Universe` — `paramId`, `paramType`, `paramTypeAt` (the universe at ≤ (2a,2a)).

This module re-exports them all. Each builds a `Param` out of `Param`s for its parts, at a class governed by
the dependency tables in `Lattice`. (Parameterized prelude types like `List`/`Quot` are not here —
they are ordinary `@[trocq]` registrations under `LeTrocq/ParamLib/`.)
-/
import LeTrocq.ParamCC.Arrow
import LeTrocq.ParamCC.Forall
import LeTrocq.ParamCC.Universe
