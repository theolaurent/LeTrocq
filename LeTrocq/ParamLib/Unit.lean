/-
The LeTrocq STANDARD LIBRARY: the UNIT types — `Unit` (in `Type`) and `True` (in `Prop`).

Both register as reflexive `(4,4)` BASES (solver atoms), so a `Unit`/`True` leaf in a goal transfers and
composes with the formers. `paramUnitR`'s relation `UnitRel` is the trivial relation (`fun _ _ => PUnit`, a
subsingleton, so every field is trivial); `paramTrueR` is the reflexive identity. `True`'s value-level
translation is already covered by `paramProp`'s built-in `True` case.

(`PUnit`/`PUnit.unit` are no longer registered for the native translation: the only thing that ever met them
there was a matcher's dummy premise, reached by unfolding a `match`-defined function — and the translation no
longer unfolds, so that path is gone.)
-/
import LeTrocq.Attr
import LeTrocq.ParamCC
namespace LeTrocq.ParamLib
open LeTrocq MapClass

/-- the trivial relation on `Unit`: inhabited for any pair (`Unit` is a subsingleton). -/
def UnitRel (_a _b : Unit) : Type := PUnit

/-- `Unit ≃ Unit` at the top class — the BASE (solver atom). Every field is trivial since `Unit` is a
    subsingleton (`PUnit.unit = b` is `rfl` by structure eta). -/
@[trocq] noncomputable def paramUnitR : Param map4 map4 Unit Unit where
  R := UnitRel
  cov :=
    { map := fun _ => PUnit.unit
      map_in_R := fun _ _ _ => PUnit.unit          -- the relation `UnitRel _ _` is itself `PUnit`
      R_in_map := fun _ _ _ => rfl
      R_in_mapK := fun _ _ _ => rfl }
  contra :=
    { map := fun _ => PUnit.unit
      map_in_R := fun _ _ _ => PUnit.unit
      R_in_map := fun _ _ _ => rfl
      R_in_mapK := fun _ _ _ => rfl }

/-- `True ≃ True` (in `Prop`) — the reflexive identity, the `Prop`-level unit. A solver base. -/
@[trocq] def paramTrueR : Param map4 map4 True True := paramRefl True

end LeTrocq.ParamLib
