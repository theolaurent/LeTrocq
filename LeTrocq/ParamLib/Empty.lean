/-
The LeTrocq STANDARD LIBRARY: the EMPTY types — `Empty` (in `Type`) and `False` (in `Prop`).

Both are registered as reflexive `(4,4)` BASES (`Param … X X := paramRefl X`): a type with NO constructors
needs no constructor TERM primitives and no parameterized former — the diagonal identity equivalence is the
whole story. A base (no argument binders, both sides a closed constant) installs as a solver ATOM, so a goal
mentioning `Empty`/`False` as a leaf transfers — e.g. `Empty` in a codomain, or `False` inside a negation
`¬P = P → False`.

`False`'s value-level translation is already covered by `paramProp` (which special-cases the `Prop`
connectives `True`/`False`); this base is what the `trocq`/`transfer%` SOLVER additionally needs.
-/
import LeTrocq.Attr
import LeTrocq.ParamCC
namespace LeTrocq.ParamLib
open LeTrocq MapClass

/-- `Empty ≃ Empty` (in `Type`) — the reflexive identity. A solver atom; no constructors, so nothing else. -/
@[trocq] def paramEmptyR : Param map4 map4 Empty Empty := paramRefl Empty

/-- `False ≃ False` (in `Prop`) — the reflexive identity, the `Prop`-level empty. -/
@[trocq] def paramFalseR : Param map4 map4 False False := paramRefl False

end LeTrocq.ParamLib
