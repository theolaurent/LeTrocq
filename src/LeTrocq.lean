/-
LeTrocq — a Lean-native reformulation of modular parametricity / proof transfer. Four layers:

  Core/        — the choice-free object logic: the MapClass/ParamClass lattice (`Class`) and the graded
                 witness records `Param m n A B` with their weakening maps (`Param`).
  Combinators/ — the graded type-theory combinators (`Universe`/`Arrow`/`Forall`): a `Param` for a sort /
                 `A → B` / `∀ x, B x` from `Param`s for its parts, at any output class.
  Driver/      — the `MetaM` metaprogram: the `@[trocq]` `Registry`, the term translation `⟨·⟩`
                 (`Counterpart`), the demand-driven relational translation `[·]` (`Transfer`, whose
                 `assemble` walks a type top-down at the minimal class each part needs), and the user-facing
                 elaborators `transfer`/`trocq`/`translate`/`relate` (`Tactic`).
  Lib/         — `@[trocq]` registrations for prelude types, so `import LeTrocq` transfers over them out of
                 the box. Ground types (`Bool`, `Nat`, …) need none: a type whose counterpart is itself is
                 short-circuited to the diagonal `paramRefl`, which a user equivalence (`Nat ≃ Unary`) overrides.
-/
import LeTrocq.Core.Class
import LeTrocq.Core.Param
import LeTrocq.Combinators
import LeTrocq.Driver.Registry
import LeTrocq.Driver.Counterpart
import LeTrocq.Driver.Transfer
import LeTrocq.Driver.Tactic
import LeTrocq.Lib
