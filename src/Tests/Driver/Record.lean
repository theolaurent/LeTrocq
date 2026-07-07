/-
Registering a STRUCTURE (record) whose parametricity relation is itself a `structure`: tagging `@[trocq]
structure PtR` auto-registers ALL its parts as term primitives — each FIELD projection (`Pt.x`/`Pt.y`) and the
constructor (`Pt.mk`) — with NO hand-written proxy. Exercises the structure branch of
`Registry.deriveRelationPrims` (`deriveStructureCtorPrim` + the projection registrations) end-to-end over
`Nat ≃ Unary`, on both surfaces.
-/
import LeTrocq
import Examples.Record
import Examples.NatUnary
namespace LeTrocq.Tests
open LeTrocq MapClass LeTrocq.Examples

/- ===================== the TYPE surface (`transfer%` / `trocq`, via the graded `paramPt`) ===================== -/
-- the forward transport builds a `Pt Unary` from a `Pt Nat`, field by field, and COMPUTES.
example : (transfer% (Pt Nat) to (Pt Unary)).cov.map (Pt.mk 0 1) = { x := Unary.z, y := Unary.s Unary.z } := rfl
-- and the backward transport (contra map) computes too.
example : (transfer% (Pt Nat) to (Pt Unary)).contra.map { x := Unary.z, y := Unary.s Unary.z } = Pt.mk 0 1 := rfl

-- a goal over `Pt Unary` transfers to the `Nat` side.
example : ∀ p : Pt Unary, p.x = p.x := by
  trocq            -- ⊢ ∀ p : Pt Nat, p.x = p.x
  exact fun p => rfl

/- ===================== the TERM surface — the CONSTRUCTOR primitive (`Pt.mk`, auto-derived) ===================== -/
-- `⟨Pt.mk 0 1⟩ = { x := Unary.z, y := Unary.s Unary.z }` — the constructor crosses with no proxy.
example : (translate% (Pt.mk 0 1 : Pt Nat)) = ({ x := Unary.z, y := Unary.s Unary.z } : Pt Unary) := rfl
-- its relatedness witness elaborates (uses `Pt.mk.trocqPrim`).
noncomputable def mkWit := relate% (Pt.mk 0 1 : Pt Nat)

/- ===================== the TERM surface — the FIELD projections (`Pt.x`/`Pt.y`, auto-derived) ===================== -/
-- `⟨(Pt.mk 3 4).x⟩` crosses via the auto-registered projection `PtR.xR`, and computes.
example : (translate% ((Pt.mk 3 4 : Pt Nat).x)) = Unary.s (Unary.s (Unary.s Unary.z)) := rfl
example : (translate% ((Pt.mk 3 4 : Pt Nat).y)) = Unary.s (Unary.s (Unary.s (Unary.s Unary.z))) := rfl
-- a projection under a λ-bound point (uses `paramPt` for the binder's relation + the projection primitive).
noncomputable def projWit := relate% (fun (p : Pt Nat) => p.x)
example : (translate% (fun (p : Pt Nat) => p.x)) = (fun (p : Pt Unary) => p.x) := rfl

end LeTrocq.Tests
