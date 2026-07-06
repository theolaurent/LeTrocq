/-
The map/comap-carrying COMBINATORS — one construction per file under `LeTrocq/Combinators/`:

  • `LeTrocq.Combinators.Arrow`    — `RArrow`, the graded `paramArrow`.
  • `LeTrocq.Combinators.Forall`   — `RForall`, the graded dependent-Π `paramForall`.
  • `LeTrocq.Combinators.Universe` — `paramRefl`/`paramTypeAtInner`/`paramProp` (the universe combinators, `Type` capped at (2a,2a)).

This module re-exports them all. Each builds a `Param` out of `Param`s for its parts, at a class governed by
the per-former variance table that lives with it (`arrowVariance`/`forallVariance`; the universe has a fixed
cap). (Parameterized prelude types like `List`/`Quot` are not here — they are ordinary `@[trocq]`
registrations under `LeTrocq/Lib/`.)
-/
import LeTrocq.Combinators.Arrow
import LeTrocq.Combinators.Forall
import LeTrocq.Combinators.Universe
