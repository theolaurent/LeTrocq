/-
Worked example: a NON-ATOMIC ground type — `List Unit ≃ Nat`.

The equivalence `Nat ≃ Unary` (see `NatUnary`) registers a bare CONSTANT on each side. Here the source is a
COMPOUND closed type, `List Unit`: a list of units IS a unary numeral (its length). `@[trocq]` accepts a
`Param m n A B` whose sides are any closed types (not just constants) and files it as a GROUND base — matched
WHOLE by `isDefEq`, so `List Unit` behaves as an opaque atom equivalent to `Nat`, overriding the structural
`List` relator and the whole-diagonal short-circuit that would otherwise send `List Unit ↦ List Unit`.

  • `RLU`     : the ground base, `Param (4,4) (List Unit) Nat`   (length / replicate)
  • `lzero`/`lsucc` + `LZeroR`/`LSuccR` : the List side's unary "constructors" and their term primitives,
    so terms transfer LEAF-BY-LEAF (`⟨lsucc l⟩ = Nat.succ ⟨l⟩`) exactly as `Nat.zero`/`Nat.succ` do.

A NOTE ON TERM TRANSLATION. `List Unit` and `Nat` have DIFFERENT constructor shapes (`List.cons` carries a
`Unit`; `Nat.succ` does not), so the arity-preserving `⟨·⟩` cannot cross a raw `List.cons` to `Nat.succ`.
Two consistent ways to move terms, both shown below:
  1. TRANSPORT a term through the equivalence MAP — `(transfer% (List Unit)).cov.map` is `List.length`, so it
     sends ANY `List Unit` (including a literal `[(), ()]`) to a `Nat`. This is what the equivalence gives for
     free, no per-term registration.
  2. REBUILD leaf-by-leaf via registered primitives — but only for terms written with `lzero`/`lsucc` (the
     arity-matching constructors), for which `translate%`/`relate%` produce the native `Nat` term and its
     relatedness. A raw `[(), ()]` is NOT built from these, so it goes route 1.
-/
import LeTrocq
namespace LeTrocq.Examples
open LeTrocq MapClass

/- ===================== the ground equivalence `List Unit ≃ Nat` ===================== -/
/-- related when the list's length is the number. `PLift` of an equality, hence a subsingleton — the `(4,4)`
    coherence is free by proof irrelevance, no univalence (just like `RN`). -/
def RLUN : List Unit → Nat → Type := fun l n => PLift (l.length = n)

/-- every `List Unit` is `replicate` of its own length (all elements are `()`), the section round-trip. -/
theorem replicate_length_unit : ∀ l : List Unit, List.replicate l.length () = l
  | []      => rfl
  | () :: t => by rw [List.length_cons, List.replicate_succ, replicate_length_unit t]

@[trocq] def RLU : Param map4 map4 (List Unit) Nat where
  R := RLUN
  cov :=
    { map := List.length
      mapInR := fun _ _ h => PLift.up h
      rInMap := fun _ _ r => r.down
      rInMapK := fun _ _ _ => rfl }
  contra :=
    { map := fun n => List.replicate n ()
      mapInR := fun _ _ h => PLift.up (by subst h; exact List.length_replicate)
      rInMap := fun _ l r => by have h := r.down; rw [← h]; exact replicate_length_unit l
      rInMapK := fun _ _ r => by cases r; rfl }

/- ===================== the List side's unary "constructors" + their term primitives ===================== -/
/-- zero = the empty list. -/
def lzero : List Unit := []
/-- successor = prepend a unit. Arity-matches `Nat.succ` (one argument), so `⟨·⟩` can cross it. -/
def lsucc (l : List Unit) : List Unit := () :: l

/-- `lzero ↦ Nat.zero`. -/
@[trocq] def LZeroR : RLUN lzero Nat.zero := PLift.up rfl
/-- `lsucc ↦ Nat.succ`: prepending a unit corresponds to taking the successor. -/
@[trocq] def LSuccR (l : List Unit) (n : Nat) (r : RLUN l n) : RLUN (lsucc l) (Nat.succ n) :=
  PLift.up (by show (() :: l).length = Nat.succ n; rw [List.length_cons, r.down])

/- ===================== worked usage ===================== -/

-- the ground base overrides the diagonal: `⟨List Unit⟩ = Nat`, and the relation is `RLUN`, not `PLift (a = b)`.
example : (translate% (List Unit)) = Nat := rfl
example : (transfer% (List Unit)).R = RLUN := rfl

-- ROUTE 1 — transport a raw list through the map (`= List.length`); works for any `List Unit`.
example : (transfer% (List Unit)).cov.map [(), ()] = 2 := rfl
example : (transfer% (List Unit)).contra.map 3 = [(), (), ()] := rfl

-- ROUTE 2 — LEAF-BY-LEAF term translation via the registered constructors.
example : (translate% lsucc) = Nat.succ := rfl
example : (translate% (fun l => lsucc l)) = (fun n => Nat.succ n) := rfl
example : (translate% (lsucc (lsucc lzero))) = 2 := rfl
-- ... and its relatedness (the proof the counterpart is correct).
example : RLUN (lsucc (lsucc lzero)) 2 := relate% (lsucc (lsucc lzero))
-- backward too: `⟨Nat.succ⟩ = lsucc`, `⟨Nat⟩ = List Unit`.
example : (translate% (fun n : Nat => Nat.succ n)) = (fun l => lsucc l) := rfl

-- ground type nested under a former: `(List Unit → List Unit)` transfers to `Nat → Nat`, and computes.
example : (transfer% (List Unit → List Unit)).cov.map lsucc 2 = 3 := rfl

-- a goal over `List Unit` transfers to `Nat`.
example : List Unit := by trocq; exact 3

end LeTrocq.Examples
