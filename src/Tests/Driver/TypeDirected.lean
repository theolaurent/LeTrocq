/- Type-directed ground-type selection: multiple registered equivalences for one source type, chosen by an
   explicit `to` target. Exercises the pair-indexed registries + the `tgt?` threading through `assemble` /
   `assembleTerm` / `Counterpart.term`. Imports `Examples.NatUnary` for the `Nat ≃ Unary` base and registers a
   SECOND `Nat ≃ Wrap` base here — the two must coexist (no clobber) and be selectable by target. -/
import LeTrocq
import Examples.NatUnary
namespace LeTrocq.Tests
open LeTrocq MapClass LeTrocq.Examples

/- ===================== a SECOND equivalence for `Nat`, distinct target head `Wrap` ===================== -/
structure Wrap where
  val : Nat
deriving Repr

def RNW : Nat → Wrap → Type := fun n w => PLift (w.val = n)
@[trocq] def RNWit : Param map4 map4 Nat Wrap where
  R := RNW
  cov := { map := Wrap.mk
           mapInR := fun n w h => PLift.up (by subst h; rfl)
           rInMap := fun n w r => by obtain ⟨v⟩ := w; exact congrArg Wrap.mk r.down.symm
           rInMapK := fun _ _ _ => rfl }
  contra := { map := Wrap.val
              mapInR := fun w n h => PLift.up h
              rInMap := fun w n r => r.down
              rInMapK := fun _ _ _ => rfl }

/- ===================== (1) type-directed ATOM selection ===================== -/
-- the SAME source `Nat → Nat` maps its codomain to `Unary` or `Wrap` per the `to` target (domain stays the
-- diagonal `Nat`, because the target domain is `Nat`); both registrations coexist, neither clobbered.
-- (both selections compute — if the second registration had clobbered the first, one `to` would error.)
example : (transfer from (Nat → Nat) to (Nat → Unary)).cov.map (· + 1) 0 = Unary.s Unary.z := rfl
example : (transfer from (Nat → Nat) to (Nat → Wrap)).cov.map  (· + 1) 0 = Wrap.mk 1 := rfl

/- ===================== (2) a parameterized former retargets its element ===================== -/
example : (transfer from (List Nat) to (List Unary)).cov.map [0, 1] = [Unary.z, Unary.s Unary.z] := rfl
example : (transfer from (List Nat) to (List Wrap)).cov.map  [0, 1] = [Wrap.mk 0, Wrap.mk 1] := rfl

/- ===================== (3) the `0`-SPLIT — term-level target selection ===================== -/
-- transfer `∀ f:Nat→Nat, f 0 = 0` to `∀ f:Nat→Unary, f 0 = Unary.z`: the inner `0` (f's `Nat` argument) stays
-- `Nat.zero`, while the RHS `0` becomes `Unary.z`. The type ASCRIPTION forces the counterpart to be EXACTLY
-- the requested target — it only typechecks if the two `0`s were split by their propagated targets.
noncomputable def zeroSplit :
    Param map4 map4 (∀ f : Nat → Nat, f 0 = 0) (∀ f : Nat → Unary, f 0 = Unary.z) :=
  transfer from (∀ f : Nat → Nat, f 0 = 0) to (∀ f : Nat → Unary, f 0 = Unary.z)

/- ===================== (4) SYNTH (no `to`) unchanged: preferred = last-registered = `Wrap` ===================== -/
example : (transfer from (Nat → Nat)).cov.map (· + 1) (Wrap.mk 0) = Wrap.mk 1 := rfl

/- ===================== (5) `trocq to G'` selects the target goal ===================== -/
example : ∀ u : Unary, Pos u := by
  trocq to (∀ n : Nat, Pos' n)
  exact fun n => Nat.zero_le n

/- ===================== (6) `transfer to B` — source synthesized from the named target =====================
   `transfer to B` names the TARGET (right side) and synthesizes the SOURCE by the counterpart translation
   (the last-registered counterpart per head). `Unary`/`Wrap` are each the B-side of exactly one base, so
   their preferred counterpart is unambiguously `Nat` — the source is `Nat` on the left, the named target on
   the right. -/
example : (transfer to (Unary → Unary)).cov.map (· + 1) Unary.z = Unary.s Unary.z := rfl
example : (transfer to (Wrap → Wrap)).cov.map  (· + 1) (Wrap.mk 0) = Wrap.mk 1 := rfl
-- the synthesized source is `Nat` on the left, the named target on the right:
example : True := by
  have : Param map4 map4 (Nat → Nat) (Unary → Unary) := transfer to (Unary → Unary)
  trivial

end LeTrocq.Tests
