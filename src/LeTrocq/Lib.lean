/-
The LeTrocq STANDARD LIBRARY: `@[trocq]` registrations for the prelude types in Lean's library, so that
`import LeTrocq` gives transfer over them out of the box. One type per file under `Lib/`:

  • `LeTrocq.Lib.List`   — `List`   (relator + inductive relation + constructor primitives)
  • `LeTrocq.Lib.Option` — `Option` (the same recipe, smaller)
  • `LeTrocq.Lib.Array`  — `Array`  (reuses `List` through `toList`; literal head `List.toArray`)
  • `LeTrocq.Lib.Prod`   — `Prod`   (×, two type parameters, non-dependent)
  • `LeTrocq.Lib.Sum`    — `Sum`    (⊕, two type parameters, two constructors)
  • `LeTrocq.Lib.Sigma`  — `Sigma`  (Σ, dependent — exercises the type-FAMILY relator machinery)
  • `LeTrocq.Lib.Quot`   — `Quot`   (the kernel quotient: type former + constructor + graded relator)
  • `LeTrocq.Lib.Eq`     — `Eq`    (propositional equality, as a relator over the related type)
  • `LeTrocq.Lib.Logic`  — `Not`/`And`/`Or`/`Iff`  (the connectives, as `Prop` relators)

These are ordinary user-level registrations (each could live verbatim in a downstream project); they ship
with the library only because their types are in the prelude. The driver knows NO type intrinsically — even
the kernel constant `Quot` registers here via `@[trocq]`. Non-prelude examples of registration
(a W-type) stay under `Examples/`.

Ground types (`Bool`, `Nat`, `Empty`, `Unit`, `True`, `False`) have NO registration file: a type/term whose
counterpart is itself is short-circuited to the generic diagonal `paramRefl` in `Transfer` (relation
`PLift (a = b)`, identity maps), so they transfer to themselves with no per-type witness — and a user
equivalence like `Nat ≃ Unary` overrides that diagonal whenever it applies.
-/
import LeTrocq.Lib.List
import LeTrocq.Lib.Option
import LeTrocq.Lib.Array
import LeTrocq.Lib.Prod
import LeTrocq.Lib.Sum
import LeTrocq.Lib.Sigma
import LeTrocq.Lib.Quot
import LeTrocq.Lib.Eq
import LeTrocq.Lib.Logic
