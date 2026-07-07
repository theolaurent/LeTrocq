/-
Transferring the mathematical structure of a GROUP (see `Examples/Group.lean`). We register a concrete carrier
equivalence `Bool ≃ Parity` and the group ℤ/2ℤ on `Bool` (`mul = xor`, `one = false`, `inv = id`), then:
  • `transfer%` transports the WHOLE group `Group Bool → Group Parity` (operations AND axioms) — and it COMPUTES;
  • the auto-registered operation primitives (`Group.mul`/`Group.one`/`Group.inv`) cross the term surface;
  • `trocq` proves a group law on the `Parity` side by transferring it to `Bool`.
-/
import LeTrocq
import Examples.Group
namespace LeTrocq.Tests
open LeTrocq MapClass LeTrocq.Examples

/- ===================== a concrete carrier equivalence `Bool ≃ Parity` ===================== -/
inductive Parity | even | odd deriving Repr, DecidableEq
def Parity.toBool : Parity → Bool | .even => false | .odd => true
def boolToParity : Bool → Parity | false => .even | true => .odd

def RBoolParity : Bool → Parity → Type := fun b p => PLift (p.toBool = b)
@[trocq] def RBP : Param map4 map4 Bool Parity where
  R := RBoolParity
  cov :=
    { map := boolToParity
      mapInR := fun b p h => PLift.up (by subst h; cases b <;> rfl)
      rInMap := fun b p r => by have h := r.down; subst h; cases p <;> rfl
      rInMapK := fun _ _ _ => rfl }
  contra :=
    { map := Parity.toBool
      mapInR := fun p b h => PLift.up h
      rInMap := fun p b r => r.down
      rInMapK := fun _ _ _ => rfl }

/- ===================== the group ℤ/2ℤ on `Bool` (all laws by `decide`) ===================== -/
def boolGroup : Group Bool where
  mul a b := a != b
  one := false
  inv a := a
  mul_assoc := by decide
  one_mul := by decide
  inv_mul := by decide

/- ===================== (1) transporting the whole group — and it COMPUTES ===================== -/
-- the transported group on `Parity` (ℤ/2ℤ moved across `Bool ≃ Parity`); its operations compute.
noncomputable def parityGroup : Group Parity := (transfer% (Group Bool) to (Group Parity)).cov.map boolGroup
-- `mul`: `odd * odd = even`, `odd * even = odd`; `one = even`; `inv odd = odd`.
example : parityGroup.mul Parity.odd Parity.odd = Parity.even := rfl
example : parityGroup.mul Parity.odd Parity.even = Parity.odd := rfl
example : parityGroup.one = Parity.even := rfl
example : parityGroup.inv Parity.odd = Parity.odd := rfl

/- ===================== (2) the auto-registered operation primitives cross the term surface ===================== -/
-- `Group.mul`/`Group.inv` cross under λ-bound group + element (uses `paramGroup` + the projection primitives).
example : (translate% (fun (g : Group Bool) (a : Bool) => g.mul a (g.inv a)))
        = (fun (g : Group Parity) (a : Parity) => g.mul a (g.inv a)) := rfl
noncomputable def opWit := relate% (fun (g : Group Bool) (a : Bool) => g.mul a a)

/- ===================== (3) prove a group law on `Parity` by transferring it to `Bool` ===================== -/
example : ∀ (g : Group Parity) (a : Parity), g.mul g.one a = a := by
  trocq                       -- ⊢ ∀ (g : Group Bool) (a : Bool), g.mul g.one a = a
  exact fun g a => g.one_mul a

end LeTrocq.Tests
