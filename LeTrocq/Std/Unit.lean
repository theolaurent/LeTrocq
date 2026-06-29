/-
The LeTrocq STANDARD LIBRARY: `PUnit` (the matcher dummy).

`PUnit` is the placeholder a NON-RECURSIVE matcher introduces (its `casesOn` carries a `PUnit` minor premise),
so the native translation meets it whenever it crosses such a `match`. It registers like any other prelude
type — NOT as a hardcoded kernel primitive: `UnitRel` is its parametricity relation (a TYPE FORMER, so
`paramType` can cross `PUnit`) and `UnitR` is the relatedness of its unique element (a TERM primitive).

Both are UNIVERSE-POLYMORPHIC (over the dummy's universe). The dummy's level is content-free — nothing in the
irrelevant `PUnit` would pin a fresh level mvar — so the translation reuses the OCCURRENCE's level for a
homogeneous former (`relevelHomogeneous` in `LeTrocq.Translate`); it does NOT need these pinned at a fixed
universe. (`Unit` itself reduces to `PUnit.{1}`, so the translation always meets the dummy as `PUnit`.)

Only the TRANSLATION (`translate%` / `relate%`) needs it — the dummy appears in TERM position, never as a goal
type — so there is no `(4,4)` relator and nothing for the solver/tactic path.
-/
import LeTrocq.Attr
namespace LeTrocq.Std

/-- the parametricity relation of `PUnit`: the trivial relation, inhabited for ANY pair (the dummy is
    irrelevant, so all that matters is that related dummies exist). A TYPE FORMER keyed by `PUnit`. One
    universe `u` (both sides share it, as `Param (A B : Sort u)` does) so the driver can re-level it. -/
@[trocq] def UnitRel.{u} (_a _b : PUnit.{u}) : Type := PUnit

/-- `PUnit.unit` relates to itself, inhabiting the trivial relation. A TERM primitive keyed by `PUnit.unit`. -/
@[trocq] def UnitR.{u} : UnitRel.{u} PUnit.unit.{u} PUnit.unit.{u} := PUnit.unit

end LeTrocq.Std
