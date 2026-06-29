/-
The LeTrocq STANDARD LIBRARY: `PUnit` (the matcher dummy).

`PUnit` is the placeholder a NON-RECURSIVE matcher introduces (its `casesOn` carries a `PUnit` minor premise),
so the native translation meets it whenever it crosses such a `match`. It registers like any other prelude
type — NOT as a hardcoded kernel primitive: `UnitRel` is its parametricity relation (a TYPE FORMER, so
`paramType` can cross `PUnit`) and `UnitR` is the relatedness of its unique element (a TERM primitive).

Only the TRANSLATION (`translate%` / `relate%`) needs it — the dummy appears in TERM position, never as a goal
type — so there is no `(4,4)` relator and nothing for the solver/tactic path.
-/
import LeTrocq.Attr
namespace LeTrocq.Std

/- The matcher dummy is always `Unit` (= `PUnit.{1}`, `Type 0`): a nullary constructor's field-product is
   `Unit`, whatever the motive's universe. So these are MONOMORPHIC at `PUnit.{1}` — a universe-polymorphic
   `UnitRel`/`UnitR` would leave the dummy's level unconstrained (nothing in the irrelevant `PUnit` pins it),
   and the registration path (which can't reuse an occurrence's level) would then produce a counterpart at the
   wrong universe. Pinning the level here keeps `Quot`/`PUnit` plain `@[trocq]` registrations — no driver
   primitive table. (`Unit` itself reduces to `PUnit.{1}`, so the translation always meets it as `PUnit`.) -/

/-- the parametricity relation of `PUnit`: the trivial relation, inhabited for ANY pair (the dummy is
    irrelevant, so all that matters is that related dummies exist). A TYPE FORMER keyed by `PUnit`. -/
@[trocq] def UnitRel (_a _b : PUnit.{1}) : Type := PUnit.{1}

/-- `PUnit.unit` relates to itself, inhabiting the trivial relation. A TERM primitive keyed by `PUnit.unit`. -/
@[trocq] def UnitR : UnitRel PUnit.unit.{1} PUnit.unit.{1} := PUnit.unit.{1}

end LeTrocq.Std
