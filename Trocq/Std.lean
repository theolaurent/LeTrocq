/-
The Trocq STANDARD LIBRARY: `@[trocq]` registrations for the parameterized types in Lean's prelude, so that
`import Trocq` gives transfer over them out of the box. One type per file under `Std/`:

  • `Trocq.Std.List`   — `List`   (relator + inductive relation + constructor primitives)
  • `Trocq.Std.Option` — `Option` (the same recipe, smaller)
  • `Trocq.Std.Sigma`  — `Sigma`  (Σ, dependent — exercises the type-FAMILY relator machinery)

These are ordinary user-level registrations (each could live verbatim in a downstream project); they ship
with the library only because their types are in the prelude. Kernel primitives that the driver must know
INTRINSICALLY (not via `@[trocq]`) live in `Trocq/Combinators/` instead — e.g. `Quot`. Non-prelude examples
of registration (a W-type) stay under `Examples/`.
-/
import Trocq.Std.List
import Trocq.Std.Option
import Trocq.Std.Sigma
