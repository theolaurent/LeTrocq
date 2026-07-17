/-

The LeTrocq "standard library": `@[trocq]` registrations for parameterized prelude types.
These are ordinary user-level registrations, the driver knows no type intrinsically.
Ground types (`Bool`, `Nat`, etc.) need none: their counterpart is themselves, so they
short-circuit to the diagonal `paramRefl`.

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
