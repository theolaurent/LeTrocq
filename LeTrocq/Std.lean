/-
The LeTrocq STANDARD LIBRARY: `@[trocq]` registrations for the parameterized types in Lean's prelude, so that
`import LeTrocq` gives transfer over them out of the box. One type per file under `Std/`:

  • `LeTrocq.Std.List`   — `List`   (relator + inductive relation + constructor primitives)
  • `LeTrocq.Std.Option` — `Option` (the same recipe, smaller)
  • `LeTrocq.Std.Sigma`  — `Sigma`  (Σ, dependent — exercises the type-FAMILY relator machinery)

These are ordinary user-level registrations (each could live verbatim in a downstream project); they ship
with the library only because their types are in the prelude. Kernel primitives that the driver must know
INTRINSICALLY (not via `@[trocq]`) live in `LeTrocq/Core/` instead — e.g. `Quot`. Non-prelude examples
of registration (a W-type) stay under `Examples/`.
-/
import LeTrocq.Std.List
import LeTrocq.Std.Option
import LeTrocq.Std.Sigma
