/-
The worked example: register the base equivalence `Nat ≃ Unary` and a few operations over it.

This is NOT part of the `LeTrocq` library — it is what a *user* writes: define your types, prove the
relatedness witnesses, tag them `@[trocq]`, and the driver (`transfer%` / `trocq` / `translate%`) picks
them up from the environment extension. The tests import this module to exercise the machinery.

  • `RN`     : the base, `Param (4,4) Nat Unary`               (a full equivalence)
  • `R0`/`Rsucc` : term primitives `Nat.zero ↦ Unary.z`, `Nat.succ ↦ Unary.s`  (for `translate%`)
  • `PosR`   : a relator for the predicate `Pos`                (for the generic `app` rule)
-/
import LeTrocq
namespace LeTrocq.Examples
open LeTrocq MapClass

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
  cov := { map := Unary.ofNat, mapInR := fun n u h => PLift.up (by subst h; exact Unary.toNat_ofNat n),
           rInMap := fun n u r => by have h := r.down; rw [← h, Unary.ofNat_toNat],
           rInMapK := fun _ _ _ => rfl }
  contra := { map := Unary.toNat, mapInR := fun u n h => PLift.up h,
              rInMap := fun u n r => r.down, rInMapK := fun _ _ _ => rfl }

/-- the base read backward, `Unary ≃ Nat` (the `trocq` tactic also gets this for free via `Param.sym`). -/
def RNsym : Param map4 map4 Unary Nat := RN.sym

/- ===================== term primitives (for the term translation `⟨·⟩` / `[·]`) ===================== -/
@[trocq] def R0 : RNU Nat.zero Unary.z := PLift.up rfl
@[trocq] def Rsucc (n : Nat) (u : Unary) (h : RNU n u) : RNU (Nat.succ n) (Unary.s u) :=
  PLift.up (by show u.toNat + 1 = Nat.succ n; rw [h.down])

/- ===================== the recursor primitive: `Nat.rec ↦ Unary.rec` =====================
   The parametricity of the eliminator: given related motives/base/step and `RNU n m`, the two recursors
   produce related results. Registering this lets the term translation CROSS `Nat.rec`, so any function
   defined by recursion on `Nat` transports to native `Unary` recursion (the motive `M : Nat → Type` is
   itself transported — `param` routes it through the type-level translation). Monomorphic at `Type` (the
   function-transport case); a universe-polymorphic recursor witness is future work. The proof is the
   standard induction: the relation `RNU n m` fixes `n = m.toNat`, after which the recursors compute. -/
@[trocq] noncomputable def NatRecR
    {M : Nat → Type} {M' : Unary → Type}
    (MR : (n : Nat) → (m : Unary) → RNU n m → M n → M' m → Type)
    (z : M 0) (z' : M' .z) (zR : MR 0 .z R0 z z')
    (s : (n : Nat) → M n → M (n + 1)) (s' : (m : Unary) → M' m → M' m.s)
    (sR : (n : Nat) → (m : Unary) → (nm : RNU n m) → (a : M n) → (a' : M' m) → MR n m nm a a' →
          MR (n + 1) m.s (Rsucc n m nm) (s n a) (s' m a')) :
    (n : Nat) → (m : Unary) → (nm : RNU n m) →
      MR n m nm (Nat.rec (motive := M) z s n) (Unary.rec (motive := M') z' s' m) := by
  intro n m
  induction m generalizing n with
  | z => intro nm; have h : n = 0 := nm.down.symm; subst h; exact zR
  | s m₀ ih => intro nm; have h : n = m₀.toNat + 1 := nm.down.symm; subst h
               exact sR m₀.toNat m₀ ⟨rfl⟩ _ _ (ih m₀.toNat ⟨rfl⟩)

/- ===================== a relator for a predicate (for the generic `app` rule) ===================== -/
def Pos  (u : Unary) : Prop := 0 ≤ u.toNat
def Pos' (n : Nat)   : Prop := 0 ≤ n
@[trocq] def PosR (mc nc : MapClass) (u : Unary) (n : Nat) (uR : RNsym.R u n) : Param mc nc (Pos u) (Pos' n) :=
  paramPropFromMaps mc nc
    (fun h => by unfold Pos at h; unfold Pos'; have := uR.down; omega)
    (fun h => by unfold Pos' at h; unfold Pos;  have := uR.down; omega)

end LeTrocq.Examples
