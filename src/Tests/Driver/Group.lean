/-
Relating two DISTINCT group instances via `GroupR` (see `Examples/Group.lean`): `intGroup` (ℤ) and
`boolGroup` (ℤ/2ℤ), through the parity homomorphism ℤ ↠ ℤ/2ℤ. There is NO type equivalence `Int ≃ Bool`, so
this is a standalone correspondence, not a full transport. We exercise:
  • the parity relation `parityR` itself;
  • the TERM surface (`translate`/`relate`): the `@[trocq]` witness registers `intGroup ↦ boolGroup`;
  • `trocq` on ELEMENT goals, via the partial parity carrier `RBI : Param map4 map2a Int Bool`.
-/
import LeTrocq
import Examples.Group
namespace LeTrocq.Tests
open LeTrocq MapClass LeTrocq.Examples

/- ===================== the parity relation ===================== -/
example : parityR 0 false := ⟨by decide⟩
example : parityR 3 true := ⟨by decide⟩
example : parityR 1 true := ⟨by decide⟩
example : parityR 4 false := ⟨by decide⟩

/- ===================== the correspondence witness ===================== -/
-- the whole `GroupR` witness elaborates (its three fields — mul/one/inv — all discharge).
example : GroupR Int Bool parityR intGroup boolGroup := intBoolGroupR

/- ===================== the TERM surface (`translate` / `relate`) ===================== -/
-- the `@[trocq]` witness registers `intGroup ↦ boolGroup`, so `⟨intGroup⟩ = boolGroup`.
example : (translate intGroup) = boolGroup := rfl
-- `relate` recovers the correspondence witness.
example : GroupR Int Bool parityR intGroup boolGroup := relate intGroup

/- ===================== `trocq` on ELEMENT goals, via the parity carrier `RBI` =====================
   A group EQUATION does NOT transfer, by design: ℤ ↠ ℤ/2ℤ is non-injective, so `z + z = 0` (FALSE in ℤ)
   is not a sound counterpart of `b != b = false` (TRUE in ℤ/2ℤ). The `(4,2a)` carrier lacks the `Bool → Int`
   completeness `paramEq` needs, so the driver refuses it — that is soundness, not a gap. -/

-- but a PARITY-INVARIANT predicate transfers soundly: "z + z is even" over ℤ ⤳ "b != b is even" over ℤ/2ℤ,
-- a genuine element-level `trocq` across the homomorphism. `EvenR` is the predicate relator (`Int`-side
-- first, matching the goal); its carrier argument is the bound element's `parityR` relatedness.
def EvenI (z : Int) : Prop := z % 2 = 0
/-- `abbrev` (reducible), so `decide` sees through to `DecidableEq Bool` on the ℤ/2ℤ side. -/
abbrev EvenB (b : Bool) : Prop := b = false
@[trocq] def EvenR (mc nc : MapClass) (z : Int) (b : Bool) (h : parityR z b) :
    Param mc nc (EvenI z) (EvenB b) :=
  paramPropFromMaps mc nc
    (fun hz => by
      have hd := h.down; have hz' : z % 2 = 0 := hz
      cases b
      · rfl
      · exfalso; simp only [cond_true] at hd; omega)
    (fun hb => by
      have hb' : b = false := hb; subst hb'
      have hd := h.down; simpa [EvenI] using hd)

-- the goal uses the GENERIC `Group.mul` (instance `[Group Int]` synthesized to `intGroup`); after `trocq`
-- it is generic `Group.mul` over `[Group Bool]` — and now `decide` closes it, the whole point of landing in
-- the finite ℤ/2ℤ.
example : ∀ z : Int, EvenI (Group.mul z z) := by
  trocq          -- ⊢ ∀ b : Bool, EvenB (Group.mul b b)
  decide

end LeTrocq.Tests
