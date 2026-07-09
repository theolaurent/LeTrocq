/-
The LeTrocq standard library: `@[trocq]` registrations for prelude types (`List`, `Option`, `Array`, `Prod`,
`Sum`, `Sigma`, the kernel `Quot`, equality `Eq`, and the connectives `Not`/`And`/`Or`/`Iff`), one per file
under `Lib/`, so `import LeTrocq` transfers over them out of the box. These are ordinary user-level
registrations, shipped here only because their types are in the prelude — the driver knows no type
intrinsically. Ground types (`Bool`, `Nat`, …) need none: their counterpart is themselves, so they
short-circuit to the diagonal `paramRefl`, which a user equivalence (`Nat ≃ Unary`) overrides when it applies.
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
