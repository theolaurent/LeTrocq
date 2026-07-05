/-
The LeTrocq STANDARD LIBRARY: `@[trocq]` registrations for the prelude types in Lean's library, so that
`import LeTrocq` gives transfer over them out of the box. One type per file under `ParamLib/`:

  • `LeTrocq.ParamLib.List`   — `List`   (relator + inductive relation + constructor primitives)
  • `LeTrocq.ParamLib.Option` — `Option` (the same recipe, smaller)
  • `LeTrocq.ParamLib.Array`  — `Array`  (reuses `List` through `toList`; literal head `List.toArray`)
  • `LeTrocq.ParamLib.Prod`   — `Prod`   (×, two type parameters, non-dependent)
  • `LeTrocq.ParamLib.Sum`    — `Sum`    (⊕, two type parameters, two constructors)
  • `LeTrocq.ParamLib.Sigma`  — `Sigma`  (Σ, dependent — exercises the type-FAMILY relator machinery)
  • `LeTrocq.ParamLib.Quot`   — `Quot`   (the kernel quotient: type former + constructor + graded relator)
  • `LeTrocq.ParamLib.Eq`     — `Eq`    (propositional equality, as a relator over the related type)
  • `LeTrocq.ParamLib.Logic`  — `Not`/`And`/`Or`/`Iff`  (the connectives, as `Prop` relators)

These are ordinary user-level registrations (each could live verbatim in a downstream project); they ship
with the library only because their types are in the prelude. The driver knows NO type intrinsically — even
the kernel constant `Quot` registers here via `@[trocq]`. Non-prelude examples of registration
(a W-type) stay under `Examples/`.

Ground types (`Bool`, `Nat`, `Empty`, `Unit`, `True`, `False`) have NO registration file: a type/term whose
counterpart is itself is short-circuited to the generic diagonal `paramRefl` in `Transfer` (relation
`PLift (a = b)`, identity maps), so they transfer to themselves with no per-type witness — and a user
equivalence like `Nat ≃ Unary` overrides that diagonal whenever it applies.
-/
import LeTrocq.ParamLib.List
import LeTrocq.ParamLib.Option
import LeTrocq.ParamLib.Array
import LeTrocq.ParamLib.Prod
import LeTrocq.ParamLib.Sum
import LeTrocq.ParamLib.Sigma
import LeTrocq.ParamLib.Quot
import LeTrocq.ParamLib.Eq
import LeTrocq.ParamLib.Logic
