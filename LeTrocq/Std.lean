/-
The LeTrocq STANDARD LIBRARY: `@[trocq]` registrations for the parameterized types in Lean's prelude, so that
`import LeTrocq` gives transfer over them out of the box. One type per file under `Std/`:

  • `LeTrocq.Std.List`   — `List`   (relator + inductive relation + constructor primitives)
  • `LeTrocq.Std.Option` — `Option` (the same recipe, smaller)
  • `LeTrocq.Std.Sigma`  — `Sigma`  (Σ, dependent — exercises the type-FAMILY relator machinery)
  • `LeTrocq.Std.Quot`   — `Quot`   (the kernel quotient: type former + constructor + `(4,4)` relator)
  • `LeTrocq.Std.Unit`   — `PUnit`  (the matcher dummy: type former + element primitive, no relator)

These are ordinary user-level registrations (each could live verbatim in a downstream project); they ship
with the library only because their types are in the prelude. The driver knows NO type intrinsically — even
the kernel constants `Quot`/`PUnit` register here via `@[trocq]`. Non-prelude examples of registration
(a W-type) stay under `Examples/`.
-/
import LeTrocq.Std.List
import LeTrocq.Std.Option
import LeTrocq.Std.Sigma
import LeTrocq.Std.Quot
import LeTrocq.Std.Unit
