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
-/
import LeTrocq.Attr
namespace LeTrocq.ParamLib
open LeTrocq

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

end LeTrocq.ParamLib
