/-
Transferring a GROUP as a TYPECLASS (see `Examples/Group.lean`, where `Group`/`GroupR` are `class`es). We
register a carrier equivalence `Bool ≃ Parity`, the group ℤ/2ℤ as an `instance` on each side, and their
correspondence as a `@[trocq] instance`. Then:
  • `transfer%` transports the WHOLE group `Group Bool → Group Parity` (operations AND axioms) — it COMPUTES;
  • the auto-registered operation primitives (`Group.mul`/`Group.one`/`Group.inv`) cross the term surface;
  • the `@[trocq] instance` correspondence lets a term over the concrete `boolGroup` cross to `parityGroup`;
  • `trocq` proves a group law on the `Parity` side by transferring it to `Bool`.
Nothing here is special-cased for classes — `@[trocq]` reads the type, so `class`/`instance` register exactly
like `structure`/`def`. The relation/relator (`GroupR`/`paramGroup`) are consumed by the driver's registry,
never by `synthInstance`.
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

/- ===================== the group ℤ/2ℤ, as `instance`s related by a `@[trocq] instance` ===================== -/
/-- ℤ/2ℤ on `Bool` (`mul = xor`, `one = false`, `inv = id`); laws by `decide`. -/
instance boolGroup : Group Bool where
  mul a b := a != b
  one := false
  inv a := a
  mul_assoc := by decide
  one_mul := by decide
  inv_mul := by decide

/-- the relator, built once (`transfer%` finds the `Bool ≃ Parity` base). -/
noncomputable def gBP : Param map4 map4 (Group Bool) (Group Parity) := transfer% (Group Bool) to (Group Parity)

/-- the `Parity`-side group, as the transport of `boolGroup` — a genuine `Group Parity` instance. -/
noncomputable instance parityGroup : Group Parity := gBP.cov.map boolGroup

/-- their CORRESPONDENCE, registered as a `@[trocq] instance` — so `⟨boolGroup⟩ = parityGroup`. (Free here,
    since `parityGroup` IS the transport; a NATIVE `Parity` group would instead need a proof, often `decide`.) -/
@[trocq] noncomputable instance boolParityGroupR : GroupR Bool Parity RBoolParity boolGroup parityGroup :=
  gBP.cov.mapInR boolGroup parityGroup rfl

/- ===================== (1) transporting the whole group — and it COMPUTES ===================== -/
-- `parityGroup`'s operations (ℤ/2ℤ moved across `Bool ≃ Parity`) compute.
example : parityGroup.mul Parity.odd Parity.odd = Parity.even := rfl
example : parityGroup.mul Parity.odd Parity.even = Parity.odd := rfl
example : parityGroup.one = Parity.even := rfl
example : parityGroup.inv Parity.odd = Parity.odd := rfl

/- ===================== (2) the `@[trocq] instance` correspondence crosses a concrete-group term ============= -/
-- a term over the concrete `boolGroup` translates to the same term over `parityGroup` (uses `⟨boolGroup⟩`).
example : (translate% (fun (x y : Bool) => boolGroup.mul x y))
        = (fun (x' y' : Parity) => parityGroup.mul x' y') := rfl

/- ===================== (3) the operation primitives cross under a λ-bound (polymorphic) instance =========== -/
example : (translate% (fun (g : Group Bool) (a : Bool) => g.mul a (g.inv a)))
        = (fun (g : Group Parity) (a : Parity) => g.mul a (g.inv a)) := rfl
noncomputable def opWit := relate% (fun (g : Group Bool) (a : Bool) => g.mul a a)

/- ===================== (4) prove a group law on `Parity` by transferring it to `Bool` ===================== -/
example : ∀ (g : Group Parity) (a : Parity), g.mul g.one a = a := by
  trocq                       -- ⊢ ∀ (g : Group Bool) (a : Bool), g.mul g.one a = a
  exact fun g a => g.one_mul a

/- ===================== (5) the carrier variance is PARAMETRIC — a sub-(4,4) carrier suffices ============== -/
-- `paramGroup`'s carrier demand scales with the output: at output `(3,3)` only a `(3,3)` carrier is needed.
example : Param map3 map3 (Group Bool) (Group Parity) :=
  paramGroup map3 map3 Bool Parity (RBP.weaken (by decide) (by decide))
example : groupVariance (map3, map3) = (map3, map3) := rfl

end LeTrocq.Tests
