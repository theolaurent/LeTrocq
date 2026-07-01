/-
The LeTrocq STANDARD LIBRARY: the logical connectives (`True`, `False`, `Not`, `And`, `Or`, `Iff`).

These register as PROP PRIMITIVES at `〚Prop〛 = PLift (· ↔ ·)`: each relates a connective applied to
related propositions by the congruent equivalence (`And` via `and_congr`, `Not` via `not_congr`, …). A
connective lives identically on both sides, so its counterpart is itself (`⟨And⟩ = And`) and the two heads
coincide — `@[trocq]` classifies each as a homogeneous prop primitive keyed by the connective.

This is what makes the driver know NO connective intrinsically: the graded relational translation `[·]`
(`assembleProp`) and the counterpart translation `⟨·⟩` both resolve a connective by the ordinary `@[trocq]`
registry lookup, exactly like a user's own predicate — no hardcoded `And`/`Or`/… cases. (The `Prop`
relatedness stays the equivalence `PLift (P ↔ P')`; propositions relate at full equivalence, by design.)

Each applied connective ALSO registers a `(4,4)` RELATOR (`paramNotR`/`paramAndR`/…) so it transfers when it
HEADS a `Prop` goal (the `trocq`/`transfer%` solver path, via `assemble`'s `.app` rule) — the same dual
registration every parameterized type uses (`List` = `ListR` + `paramListR`). The relator's relation is
`〚Prop〛` itself (`(Param … Prop …).R = PLift (·↔·)`, via `paramOfIff`); it takes each part's equivalence as a
term argument and maps them to the whole's. (`True`/`False` are nullary, already solver atoms via their
`Unit`/`Empty` bases, so they need no relator.)
-/
import LeTrocq.Attr
import LeTrocq.ParamCC.Universe
namespace LeTrocq.ParamLib
open LeTrocq MapClass

/-- `True` relates to itself (the empty conjunction). -/
@[trocq] def TrueR : PLift (True ↔ True) := PLift.up Iff.rfl
/-- `False` relates to itself (the empty disjunction). -/
@[trocq] def FalseR : PLift (False ↔ False) := PLift.up Iff.rfl
/-- `¬ P ↔ ¬ P'` from `P ↔ P'`. -/
@[trocq] def NotR (P P' : Prop) (PR : PLift (P ↔ P')) : PLift (¬ P ↔ ¬ P') :=
  PLift.up (not_congr PR.down)
/-- `(P ∧ Q) ↔ (P' ∧ Q')` from the two component equivalences. -/
@[trocq] def AndR (P P' : Prop) (PR : PLift (P ↔ P')) (Q Q' : Prop) (QR : PLift (Q ↔ Q')) :
    PLift ((P ∧ Q) ↔ (P' ∧ Q')) := PLift.up (and_congr PR.down QR.down)
/-- `(P ∨ Q) ↔ (P' ∨ Q')` from the two component equivalences. -/
@[trocq] def OrR (P P' : Prop) (PR : PLift (P ↔ P')) (Q Q' : Prop) (QR : PLift (Q ↔ Q')) :
    PLift ((P ∨ Q) ↔ (P' ∨ Q')) := PLift.up (or_congr PR.down QR.down)
/-- `(P ↔ Q) ↔ (P' ↔ Q')` from the two component equivalences. -/
@[trocq] def IffR (P P' : Prop) (PR : PLift (P ↔ P')) (Q Q' : Prop) (QR : PLift (Q ↔ Q')) :
    PLift ((P ↔ Q) ↔ (P' ↔ Q')) := PLift.up (iff_congr PR.down QR.down)

/- ===================== the `(4,4)` relators (for the `trocq` / `transfer%` solver path) =====================
   `⋆ P Q ≃ ⋆ P' Q'` from the parts' equivalences, carrying `〚Prop〛 = PLift (·↔·)` as its relation (via
   `paramOfIff`). Each part is a `Prop` argument taken as a `Param map1 map1` (a TYPE argument, like `Prod`'s
   two parameters) — so `assemble` builds each part's witness recursively and reads its counterpart off the
   `Param`, never invoking `⟨·⟩` on a relator-only head. `iffOfParam` recovers the `iff` the congruence wants. -/
@[trocq] def paramNotR (P P' : Prop) (PR : Param map1 map1 P P') :
    Param map4 map4 (¬ P) (¬ P') := paramOfIff (not_congr (iffOfParam PR))
@[trocq] def paramAndR (P P' : Prop) (PR : Param map1 map1 P P') (Q Q' : Prop) (QR : Param map1 map1 Q Q') :
    Param map4 map4 (P ∧ Q) (P' ∧ Q') := paramOfIff (and_congr (iffOfParam PR) (iffOfParam QR))
@[trocq] def paramOrR (P P' : Prop) (PR : Param map1 map1 P P') (Q Q' : Prop) (QR : Param map1 map1 Q Q') :
    Param map4 map4 (P ∨ Q) (P' ∨ Q') := paramOfIff (or_congr (iffOfParam PR) (iffOfParam QR))
@[trocq] def paramIffR (P P' : Prop) (PR : Param map1 map1 P P') (Q Q' : Prop) (QR : Param map1 map1 Q Q') :
    Param map4 map4 (P ↔ Q) (P' ↔ Q') := paramOfIff (iff_congr (iffOfParam PR) (iffOfParam QR))

end LeTrocq.ParamLib
