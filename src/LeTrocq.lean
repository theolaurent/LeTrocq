/-
LeTrocq — a Lean-native reformulation of modular parametricity / proof transfer.

The library is organised into four layers (each builds on the previous):

  Core/ — the choice-free object logic:
  • `LeTrocq.Core.Class`   — the class algebra: the MapClass/ParamClass lattice, its order/join/meet.
  • `LeTrocq.Core.Param`   — the graded witness records (`Param m n A B`) + the weakening (⇓) maps.

  Combinators/ — the graded combinators of the type theory, one construction per file:
  • `LeTrocq.Combinators.Universe` / `.Arrow` / `.Forall` — build a `Param` for a sort / `A → B` / `∀ x, B x`
    out of `Param`s for its parts, at any output class, with each part at the variance-minimal class.

  Driver/ — the metaprogram (runs in `MetaM`):
  • `LeTrocq.Driver.Registry`    — the `@[trocq]` registry: classify a witness (base / relator / term
                          primitive) from its type, store it in the env extension, and look it back up.
  • `LeTrocq.Driver.Counterpart` — the term translation `⟨·⟩`: rebuild a term's `B`-side counterpart leaf by
                          leaf (namespace `LeTrocq.Counterpart`).
  • `LeTrocq.Driver.Transfer`    — the graded relational translation `[·]`, a single demand-driven pass:
                          `assemble` walks a type top-down, pushing the demanded class through the variance
                          tables to the minimal class each part needs and building it with its graded
                          combinator (no constraint graph, no fixpoint). Its term half (`assembleTerm`) is the
                          abstraction theorem (`[t u] = [t] u ⟨u⟩ [u]`). Drives `relate` / `transfer` / `trocq`.
  • `LeTrocq.Driver.Tactic`      — the user surface: all four elaborators (`transfer`/`trocq`/`translate`/`relate`).

  Lib/ — the parametricity library: `@[trocq]` registrations for prelude types (`List`, `Option`, `Array`,
    `Prod`, `Sum`, `Sigma`, the kernel constant `Quot`, propositional equality `Eq`, and the connectives
    `Not`/`And`/`Or`/`Iff`), so `import LeTrocq` gives transfer over them out of the box. Ground types
    (`Bool`, `Nat`, `Empty`, `Unit`, `True`, `False`) need NO registration — a type/term whose counterpart is
    itself is short-circuited to the generic diagonal `paramRefl` in the driver — and a user equivalence
    (e.g. `Nat ≃ Unary`) overrides that diagonal whenever it applies.
-/
import LeTrocq.Core.Class
import LeTrocq.Core.Param
import LeTrocq.Combinators
import LeTrocq.Driver.Registry
import LeTrocq.Driver.Counterpart
import LeTrocq.Driver.Transfer
import LeTrocq.Driver.Tactic
import LeTrocq.Lib
