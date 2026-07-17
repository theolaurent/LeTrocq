/-
A class registers like structure. Here used to relate two non-isomorphic instances.
-/
import LeTrocq
namespace LeTrocq.Examples
open LeTrocq MapClass

class Group (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  inv_mul : ∀ a, mul (inv a) a = one

/- two group instances are related iff their operations correspond (group homomorphism)
   NOTE: the driver consumes it by head-lookup in the registry, not `synthInstance` -/
-- TODO: add support for implicit arguments?
@[trocq] class GroupR (A A' : Type) (RA : A → A' → Type) (g : Group A) (g' : Group A') where
  mulR : ∀ a a', RA a a' → ∀ b b', RA b b' → RA (g.mul a b) (g'.mul a' b')
  oneR : RA g.one g'.one
  invR : ∀ a a', RA a a' → RA (g.inv a) (g'.inv a')

instance boolGroup : Group Bool where
  mul a b := a != b
  one := false
  inv a := a
  mul_assoc := by decide
  one_mul := by decide
  inv_mul := by decide

instance intGroup : Group Int where
  mul a b := a + b
  one := 0
  inv a := -a
  mul_assoc := by intro a b c; omega
  one_mul := by intro a; omega
  inv_mul := by intro a; omega

/- relate an `Int` to a `Bool` by parity -/
def parityR (z : Int) (b : Bool) : Type := PLift (z % 2 = bif b then 1 else 0)

/- The `Int → Bool` map is a full retraction (map4),
   the `Bool → Int` section is sound (2a) and not complete -/
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

end LeTrocq.Examples
