/-
User-written example: a GROUP, a registered structure whose parametricity relation `GroupR` is authored as
a `@[trocq] class` relating the three operations (a signature homomorphism). Tagging it auto-registers
`Group.mul`/`Group.one`/`Group.inv` as term primitives, no proxy. `GroupR` is then used for its own sake, to
relate two DISTINCT, non-isomorphic instances — `intGroup` (ℤ) and `boolGroup` (ℤ/2ℤ) — via the parity
homomorphism ℤ ↠ ℤ/2ℤ; the partial carrier `RBI : Param map4 map2a Int Bool` lets `trocq` cross the elements.
-/
import LeTrocq
namespace LeTrocq.Examples
open LeTrocq MapClass

/- ===================== the group typeclass and its signature relation ===================== -/
/-- the mathematical structure of a group, as a Lean `class`. -/
class Group (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  inv_mul : ∀ a, mul (inv a) a = one

/-- two group instances are related iff their operations correspond (a signature homomorphism). Authored as a
    `@[trocq] class` for the class/instance parallelism, but the driver consumes it by head-lookup in the
    registry, never `synthInstance`. Tagging it auto-registers `Group.mul`/`Group.one`/`Group.inv`. -/
@[trocq] class GroupR (A A' : Type) (RA : A → A' → Type) (g : Group A) (g' : Group A') where
  mulR : ∀ a a', RA a a' → ∀ b b', RA b b' → RA (g.mul a b) (g'.mul a' b')
  oneR : RA g.one g'.one
  invR : ∀ a a', RA a a' → RA (g.inv a) (g'.inv a')

/- ===================== two concrete groups + their correspondence ===================== -/
/-- ℤ/2ℤ on `Bool` (`mul = xor`, `one = false`, `inv = id`); laws by `decide`. -/
instance boolGroup : Group Bool where
  mul a b := a != b
  one := false
  inv a := a
  mul_assoc := by decide
  one_mul := by decide
  inv_mul := by decide

/-- ℤ on `Int` (`mul = +`, `one = 0`, `inv = -·`); laws by `omega`. -/
instance intGroup : Group Int where
  mul a b := a + b
  one := 0
  inv a := -a
  mul_assoc := by intro a b c; omega
  one_mul := by intro a; omega
  inv_mul := by intro a; omega

/-- relate an `Int` to a `Bool` by parity: `z` corresponds to `b` when `z`'s parity is `b`. Oriented
    `Int`-first, so an `Int`-side `trocq` goal crosses forward (no `sym` needed). -/
def parityR (z : Int) (b : Bool) : Type := PLift (z % 2 = bif b then 1 else 0)

/-- `intGroup` and `boolGroup` correspond under parity (the homomorphism ℤ ↠ ℤ/2ℤ) — a `GroupR` witness
    between two distinct instances. Tagged `@[trocq]`, so the driver registers `intGroup ↦ boolGroup`.
    (`simp only` rather than `simp_all`, which would rewrite the mod hypotheses away from `omega`.) -/
@[trocq] def intBoolGroupR : GroupR Int Bool parityR intGroup boolGroup where
  mulR z z' hz w w' hw := ⟨by
    have h1 := hz.down; have h2 := hw.down
    cases z' <;> cases w' <;>
      simp only [boolGroup, intGroup, cond_true, cond_false, Bool.true_bne, Bool.false_bne,
        Bool.not_true, Bool.not_false] at h1 h2 ⊢ <;> omega⟩
  oneR := ⟨by decide⟩
  invR z z' hz := ⟨by
    have h := hz.down
    cases z' <;> simp only [boolGroup, intGroup, cond_true, cond_false] at h ⊢ <;> omega⟩

/- ===================== the parity CARRIER as a partial `Param` ===================== -/
/-- the parity relation as a PARTIAL `Param Int Bool`. The `Int → Bool` map is a full retraction (map4), but
    the `Bool → Int` section is sound (2a) and not complete (many ints per bool), so the carrier tops out at
    `(4, 2a)`: it crosses elements, but not equations that would need the missing `Bool → Int` completeness. -/
@[trocq] def RBI : Param map4 map2a Int Bool where
  R := parityR
  cov :=
    { map := fun z => z % 2 != 0
      mapInR := fun z b h => ⟨by
        subst h; rcases (show z % 2 = 0 ∨ z % 2 = 1 by omega) with h | h <;> rw [h] <;> decide⟩
      rInMap := fun z b r => by
        have h := r.down; cases b <;> simp only [cond_true, cond_false] at h <;> rw [h] <;> decide
      rInMapK := fun _ _ _ => rfl }
  contra :=
    { map := fun b => bif b then 1 else 0
      mapInR := fun b z h => ⟨by subst h; cases b <;> decide⟩ }

end LeTrocq.Examples
