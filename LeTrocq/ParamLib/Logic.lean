/-
The LeTrocq STANDARD LIBRARY: the logical connectives (`Not`, `And`, `Or`, `Iff`).

Each registers as a `(4,4)` RELATOR `⋆ P Q ≃ ⋆ P' Q'`, carrying `〚Prop〛 = PLift (·↔·)` as its relation (via
`paramOfIff`) — the exact same registration every parameterized type uses (`List` = `ListR` + `paramListR`,
`Prod` = `ProdR` + `paramProdR`). This is what makes the driver know NO connective intrinsically: a proposition
is a `Sort 0` type, so `assemble` crosses a connective by the ordinary `@[trocq]` relator lookup, `⟨·⟩` reads
its counterpart (`And ↦ And`) off the relator's conclusion, and `[·]` projects the relatedness `PLift (P ↔ P')`
off the `Param` — no hardcoded `And`/`Or`/… cases, and no separate prop-primitive machinery.

Each part is a `Prop` argument taken as a `Param map1 map1` (a TYPE argument, like `Prod`'s two parameters), so
`assemble` builds it recursively and reads its counterpart off the `Param`; `iffOfParam` recovers the `iff` the
congruence lemma consumes. (`True`/`False` are nullary — already solver atoms and `⟨·⟩` counterparts via their
`Unit`/`Empty` bases — so they need no entry here. The `Prop` relatedness stays the equivalence `PLift (P ↔ P')`;
propositions relate at full equivalence, by design.)
-/
import LeTrocq.Attr
import LeTrocq.ParamCC.Universe
namespace LeTrocq.ParamLib
open LeTrocq MapClass

@[trocq] def paramNotR (P P' : Prop) (PR : Param map1 map1 P P') :
    Param map4 map4 (¬ P) (¬ P') := paramOfIff (not_congr (iffOfParam PR))
@[trocq] def paramAndR (P P' : Prop) (PR : Param map1 map1 P P') (Q Q' : Prop) (QR : Param map1 map1 Q Q') :
    Param map4 map4 (P ∧ Q) (P' ∧ Q') := paramOfIff (and_congr (iffOfParam PR) (iffOfParam QR))
@[trocq] def paramOrR (P P' : Prop) (PR : Param map1 map1 P P') (Q Q' : Prop) (QR : Param map1 map1 Q Q') :
    Param map4 map4 (P ∨ Q) (P' ∨ Q') := paramOfIff (or_congr (iffOfParam PR) (iffOfParam QR))
@[trocq] def paramIffR (P P' : Prop) (PR : Param map1 map1 P P') (Q Q' : Prop) (QR : Param map1 map1 Q Q') :
    Param map4 map4 (P ↔ Q) (P' ↔ Q') := paramOfIff (iff_congr (iffOfParam PR) (iffOfParam QR))

end LeTrocq.ParamLib
