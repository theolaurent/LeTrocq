/-
Relating two distinct group instances via `GroupR`: `intGroup` (ℤ) and `boolGroup` (ℤ/2ℤ), through the parity
homomorphism ℤ ↠ ℤ/2ℤ. No type equivalence `Int ≃ Bool` — a standalone correspondence, not a full transport.
Exercises `parityR`, the term surface (`translate`/`relate`), and `trocq` on element goals via the parity
carrier `RBI : Param map4 map2a Int Bool`.
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
-- the whole `GroupR` witness elaborates (mul/one/inv fields all discharge).
example : GroupR Int Bool parityR intGroup boolGroup := intBoolGroupR

/- ===================== the TERM surface (`translate` / `relate`) ===================== -/
-- the `@[trocq]` witness registers `intGroup ↦ boolGroup`.
example : (translate intGroup) = boolGroup := rfl
-- `relate` recovers the correspondence witness.
example : GroupR Int Bool parityR intGroup boolGroup := relate intGroup

/- ===================== `trocq` on ELEMENT goals, via the parity carrier `RBI` =====================
   A group EQUATION does NOT transfer, by design: ℤ ↠ ℤ/2ℤ is non-injective, so `z + z = 0` (false in ℤ) is
   not a sound counterpart of `b != b = false` (true in ℤ/2ℤ). The `(4,2a)` carrier lacks the `Bool → Int`
   completeness `paramEq` needs, so the driver refuses it — soundness, not a gap. -/

-- but a PARITY-INVARIANT predicate transfers soundly: "z + z is even" over ℤ ⤳ "b != b is even" over ℤ/2ℤ.
-- `EvenR` is the predicate relator (`Int`-side first); its carrier arg is the bound element's `parityR`.
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

-- generic `Group.mul` over `[Group Int]` ⤳ over `[Group Bool]`; `decide` then closes it in the finite ℤ/2ℤ.
example : ∀ z : Int, EvenI (Group.mul z z) := by
  trocq          -- ⊢ ∀ b : Bool, EvenB (Group.mul b b)
  decide

/- ===================== the REVERSE direction (Bool ⤳ Int) =====================
   The mirror needs three symmetrizations to line up: the reverse `EvenR` relator (keyed under `EvenB`, via
   `symRelator`), the reverse `RBI` carrier (via `Param.sym`), and the reverse `intGroup ↔ boolGroup`
   correspondence. `intBoolGroupR` is a zero-triple `GroupR`, so `symPrimitive` leaves it unchanged (wrong
   orientation); `symStructure` reverses it field-wise. -/

-- `relate boolGroup` now has the correct reverse orientation.
example : GroupR Bool Int (fun b z => parityR z b) boolGroup intGroup := relate boolGroup

-- and the reverse `trocq` goes through: a `Bool`-side goal transfers to `Int`.
example : ∀ b : Bool, EvenB (Group.mul b b) := by
  trocq          -- ⊢ ∀ z : Int, EvenI (Group.mul z z)
  intro z; show (z + z) % 2 = 0; omega

end LeTrocq.Tests
