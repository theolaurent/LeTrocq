/-
The LeTrocq STANDARD LIBRARY: the UNIT types — `Unit` (in `Type`) and `True` (in `Prop`).

Both register as reflexive `(4,4)` BASES (solver atoms), so a `Unit`/`True` leaf in a goal transfers and
composes with the formers. `paramUnitR`'s relation `UnitRel` is the trivial relation (`fun _ _ => Unit`, a
subsingleton, so every field is trivial); `paramTrueR` is the reflexive identity. `True`'s value-level
translation is already covered by `paramProp`'s built-in `True` case.
-/
import LeTrocq.Attr
import LeTrocq.ParamCC
namespace LeTrocq.ParamLib
open LeTrocq MapClass

/-- the trivial relation on `Unit`: inhabited for any pair (`Unit` is a subsingleton). -/
def UnitRel (_a _b : Unit) : Type := Unit

/-- `Unit ≃ Unit` at the top class — the BASE (solver atom). Every field is trivial since `Unit` is a
    subsingleton (`Unit.unit = b` is `rfl` by structure eta). -/
@[trocq] noncomputable def paramUnitR : Param map4 map4 Unit Unit where
  R := UnitRel
  cov :=
    { map := fun _ => Unit.unit
      map_in_R := fun _ _ _ => Unit.unit          -- the relation `UnitRel _ _` is itself `Unit`
      R_in_map := fun _ _ _ => rfl
      R_in_mapK := fun _ _ _ => rfl }
  contra :=
    { map := fun _ => Unit.unit
      map_in_R := fun _ _ _ => Unit.unit
      R_in_map := fun _ _ _ => rfl
      R_in_mapK := fun _ _ _ => rfl }

/-- `True ≃ True` (in `Prop`) — the reflexive identity, the `Prop`-level unit. A solver base. -/
@[trocq] def paramTrueR : Param map4 map4 True True := paramRefl True

end LeTrocq.ParamLib
