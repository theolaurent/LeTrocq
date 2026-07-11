/-

  Core/          the object logic: the MapClass/ParamClass lattice and the graded
                 parametricity witnesses `Param m n A B` with their weakening maps
  Combinators/   combinators for the Calculus of Constructions: sorts and functions
  Driver/        metaprograms:
                 - term translation (`Counterpart`)
                 - relational translation (`Transfer`)
                 - user-space registration (`Registry`)
                 - user-facing elaborators (`Tactic`)
  Lib/           registrations for prelude parameterized types, so `import LeTrocq`
                 transfers over them out of the box.
-/

import LeTrocq.Core.Class
import LeTrocq.Core.Param
import LeTrocq.Combinators
import LeTrocq.Driver.Registry
import LeTrocq.Driver.Counterpart
import LeTrocq.Driver.Transfer
import LeTrocq.Driver.Tactic
import LeTrocq.Lib
