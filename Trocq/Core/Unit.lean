/-
The kernel-dummy `PUnit`: relating `PUnit` to `PUnit`.

`PUnit` is the placeholder a NON-RECURSIVE matcher introduces (its `casesOn` carries a `PUnit` minor premise),
so the native translation meets it whenever it crosses such a `match`. Like `Quot` (see `Core/Quot`), it is a
built-in PRIMITIVE the driver knows intrinsically — NOT `@[trocq]`-registered — so its parametricity lives
here in the library: the always-inhabited trivial relation, and the relatedness of the unique element.

Only the TRANSLATION needs it (the dummy appears in TERM position, never as a goal type), so there is no
solver relator — `Translate.buildCtx` seeds `UnitRel`/`UnitR` into the term/type context like a registration.
-/
namespace Trocq

/-- the parametricity relation of `PUnit`: the trivial relation, inhabited for ANY pair (the dummy is
    irrelevant, so all that matters is that related dummies exist). -/
def UnitRel (_a _b : PUnit) : Type := PUnit

/-- `PUnit.unit` relates to itself, inhabiting the trivial relation. -/
def UnitR : UnitRel PUnit.unit PUnit.unit := PUnit.unit

end Trocq
