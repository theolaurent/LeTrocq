/-
The worked example: register the base equivalence `Nat ≃ Unary` and a few operations over it.

This is NOT part of the `Trocq` library — it is what a *user* writes: define your types, prove the
relatedness witnesses, tag them `@[trocq]`, and the driver (`transfer%` / `trocq` / `translate%`) picks
them up from the environment extension. The tests import this module to exercise the machinery.

  • `RN`     : the base, `Param (4,4) Nat Unary`               (a full equivalence)
  • `R0`/`Rsucc` : term primitives `Nat.zero ↦ Unary.z`, `Nat.succ ↦ Unary.s`  (for `translate%`)
  • `PosR`   : a relator for the predicate `Pos`                (for the generic `app` rule)
-/
import Trocq
namespace Trocq.Examples
open Trocq MapClass

/- ===================== the base type and its conversions ===================== -/
inductive Unary | z | s (n : Unary) deriving Repr
namespace Unary
def toNat : Unary → Nat | .z => 0 | .s n => toNat n + 1
def ofNat : Nat → Unary | 0 => .z | n+1 => .s (ofNat n)
theorem toNat_ofNat : ∀ n, toNat (ofNat n) = n
  | 0 => rfl
  | n+1 => by show toNat (ofNat n) + 1 = n + 1; rw [toNat_ofNat n]
theorem ofNat_toNat : ∀ u, ofNat (toNat u) = u
  | .z => rfl
  | .s n => by show Unary.s (ofNat (toNat n)) = Unary.s n; rw [ofNat_toNat n]
end Unary

/- ===================== the base equivalence, registered at (4,4) ===================== -/
def RNU : Nat → Unary → Type := fun n u => PLift (u.toNat = n)
@[trocq] def RN : Param .map4 .map4 Nat Unary where
  R := RNU
  cov := { map := Unary.ofNat, map_in_R := fun n u h => PLift.up (by subst h; exact Unary.toNat_ofNat n),
           R_in_map := fun n u r => by have h := r.down; rw [← h, Unary.ofNat_toNat],
           R_in_mapK := fun _ _ _ => rfl }
  contra := { map := Unary.toNat, map_in_R := fun u n h => PLift.up h,
              R_in_map := fun u n r => r.down, R_in_mapK := fun _ _ _ => rfl }

/-- the base read backward, `Unary ≃ Nat` (the `trocq` tactic also gets this for free via `Param.sym`). -/
def RNsym : Param map4 map4 Unary Nat := RN.sym

/- ===================== term primitives (for the native translation) ===================== -/
@[trocq] def R0 : RNU Nat.zero Unary.z := PLift.up rfl
@[trocq] def Rsucc (n : Nat) (u : Unary) (h : RNU n u) : RNU (Nat.succ n) (Unary.s u) :=
  PLift.up (by show u.toNat + 1 = Nat.succ n; rw [h.down])

/- ===================== a relator for a predicate (for the generic `app` rule) ===================== -/
def Pos  (u : Unary) : Prop := 0 ≤ u.toNat
def Pos' (n : Nat)   : Prop := 0 ≤ n
@[trocq] def PosR (u : Unary) (n : Nat) (uR : RNsym.R u n) : Param map1 map1 (Pos u) (Pos' n) where
  R := fun _ _ => PLift True
  cov    := { map := fun h => by unfold Pos at h; unfold Pos'; have := uR.down; omega }
  contra := { map := fun h => by unfold Pos' at h; unfold Pos;  have := uR.down; omega }

end Trocq.Examples
