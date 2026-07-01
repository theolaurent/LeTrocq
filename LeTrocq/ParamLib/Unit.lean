/-
The LeTrocq STANDARD LIBRARY: the UNIT types — `PUnit` (in `Type`, also the matcher dummy) and `True`
(in `Prop`).

`PUnit` is the placeholder a NON-RECURSIVE matcher introduces (its `casesOn` carries a `PUnit` minor premise),
so the native translation meets it whenever it crosses such a `match`. It registers like any other prelude
type — NOT as a hardcoded kernel primitive: `UnitRel` is its parametricity relation (a TYPE FORMER, so
`paramType` can cross `PUnit`) and `UnitR` is the relatedness of its unique element (a TERM primitive).

`UnitRel`/`UnitR` are UNIVERSE-POLYMORPHIC (over the dummy's universe). The dummy's level is content-free —
nothing in the irrelevant `PUnit` would pin a fresh level mvar — so the translation reuses the OCCURRENCE's
level for a homogeneous former (`relevelHomogeneous` in `LeTrocq.Translate`); it does NOT need these pinned at
a fixed universe. (`Unit` itself reduces to `PUnit.{1}`, so the translation always meets the dummy as `PUnit`.)

The SOLVER leaf is `Unit` (the monomorphic `Type 0` unit, `Unit = PUnit.{1}`) via `paramUnitR` — a `(4,4)`
BASE whose `R` IS `UnitRel` (so it agrees with the translation). `PUnit` stays POLYMORPHIC and base-less: a
poly base can't ride the solver, which keys atoms by name and loses the occurrence's universe (unlike the
translation's `relevelHomogeneous`), and a solver goal over the unit type is the `Type 0` `Unit` anyway. The
poly multi-universe use of `PUnit` is the matcher dummy, which is the translation's job and is untouched.
`True` is the `Prop`-level unit, a reflexive base for the solver (its value-level translation is `paramProp`'s
built-in `True` case).
-/
import LeTrocq.Attr
import LeTrocq.ParamCC
namespace LeTrocq.ParamLib
open LeTrocq MapClass

/-- the parametricity relation of `PUnit`: the trivial relation, inhabited for ANY pair (the dummy is
    irrelevant, so all that matters is that related dummies exist). A TYPE FORMER keyed by `PUnit`. One
    universe `u` (both sides share it, as `Param (A B : Sort u)` does) so the driver can re-level it. -/
@[trocq] def UnitRel.{u} (_a _b : PUnit.{u}) : Type := PUnit

/-- `PUnit.unit` relates to itself, inhabiting the trivial relation. A TERM primitive keyed by `PUnit.unit`. -/
@[trocq] def UnitR.{u} : UnitRel.{u} PUnit.unit.{u} PUnit.unit.{u} := PUnit.unit

/-- `Unit ≃ Unit` (in `Type`, `Unit = PUnit.{1}`) at the top class — the BASE (solver atom). `R` is `UnitRel`
    (so it agrees with the translation's view), and every field is trivial since `Unit` is a subsingleton.
    MONOMORPHIC: `Unit` is the `Type 0` unit, and a poly base can't carry its universe through the solver. -/
@[trocq] noncomputable def paramUnitR : Param map4 map4 Unit Unit where
  R := UnitRel
  cov :=
    { map := fun _ => PUnit.unit
      map_in_R := fun _ _ _ => PUnit.unit          -- the relation `UnitRel _ _` is itself `PUnit`
      R_in_map := fun _ _ _ => rfl                 -- `PUnit.unit = b` is `rfl` by structure eta
      R_in_mapK := fun _ _ _ => rfl }
  contra :=
    { map := fun _ => PUnit.unit
      map_in_R := fun _ _ _ => PUnit.unit
      R_in_map := fun _ _ _ => rfl
      R_in_mapK := fun _ _ _ => rfl }

/-- `True ≃ True` (in `Prop`) — the reflexive identity, the `Prop`-level unit. A solver base. -/
@[trocq] def paramTrueR : Param map4 map4 True True := paramRefl True

end LeTrocq.ParamLib
