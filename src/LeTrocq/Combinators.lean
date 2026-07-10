/-
The graded combinators, re-exported: `Arrow` (`paramArrow`, now with a `Sort` codomain so `A → Prop` builds),
`Forall` (dependent-Π `paramForall`, plus its Prop-DOMAIN sibling `paramForallProp` for `P → Q` / `∀ h : P, B h`),
and `Universe` (`paramRefl`/`paramTypeAt`/`paramProp`, `Type` capped at `(2a,2a)`). Each builds a `Param` from
`Param`s for its parts, at the class its own variance table dictates. Parameterized prelude types like
`List`/`Quot` are ordinary `@[trocq]` registrations under `Lib/`, not here.
-/
import LeTrocq.Combinators.Arrow
import LeTrocq.Combinators.Forall
import LeTrocq.Combinators.Universe
