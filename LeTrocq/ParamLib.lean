/-
The LeTrocq STANDARD LIBRARY: `@[trocq]` registrations for the prelude types in Lean's library, so that
`import LeTrocq` gives transfer over them out of the box. One type per file under `ParamLib/`:

  • `LeTrocq.ParamLib.Bool`   — `Bool`   (ground inductive: diagonal relation + constructors + relator)
  • `LeTrocq.ParamLib.Nat`    — `Nat`    (the diagonal, OVERRIDABLE by a user equivalence like `Nat ≃ Unary`)
  • `LeTrocq.ParamLib.List`   — `List`   (relator + inductive relation + constructor primitives)
  • `LeTrocq.ParamLib.Option` — `Option` (the same recipe, smaller)
  • `LeTrocq.ParamLib.Array`  — `Array`  (reuses `List` through `toList`; literal head `List.toArray`)
  • `LeTrocq.ParamLib.Prod`   — `Prod`   (×, two type parameters, non-dependent)
  • `LeTrocq.ParamLib.Sum`    — `Sum`    (⊕, two type parameters, two constructors)
  • `LeTrocq.ParamLib.Sigma`  — `Sigma`  (Σ, dependent — exercises the type-FAMILY relator machinery)
  • `LeTrocq.ParamLib.Quot`   — `Quot`   (the kernel quotient: type former + constructor + `(4,4)` relator)
  • `LeTrocq.ParamLib.Unit`   — `PUnit`  (the matcher dummy: type former + element primitive, no relator)

These are ordinary user-level registrations (each could live verbatim in a downstream project); they ship
with the library only because their types are in the prelude. The driver knows NO type intrinsically — even
the kernel constants `Quot`/`PUnit` register here via `@[trocq]`. Non-prelude examples of registration
(a W-type) stay under `Examples/`.
-/
import LeTrocq.ParamLib.Bool
import LeTrocq.ParamLib.Nat
import LeTrocq.ParamLib.List
import LeTrocq.ParamLib.Option
import LeTrocq.ParamLib.Array
import LeTrocq.ParamLib.Prod
import LeTrocq.ParamLib.Sum
import LeTrocq.ParamLib.Sigma
import LeTrocq.ParamLib.Quot
import LeTrocq.ParamLib.Unit
