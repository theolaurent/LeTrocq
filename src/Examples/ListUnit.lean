/-
User-written example: a NON-ATOMIC ground type, `List Unit ≃ Nat`, with the constructors relatable for free.
`@[trocq]` files a `Param` over closed (non-constant) types as a ground base, matched whole by `isDefEq`.
The relation `RLUN` (a list of units related to its length) is an inductive, one arm per constructor pair;
tagging it auto-derives `@List.nil Unit ↦ Nat.zero` and `@List.cons Unit () ↦ Nat.succ` as ground terms, so
`[(), ()]` rebuilds to `2` with no per-constructor proxy. `RLU` is the ground base `(4,4)`, built over `RLUN`.
-/
import LeTrocq
namespace LeTrocq.Examples
open LeTrocq MapClass

/- ===================== the parametricity relation, as an inductive ===================== -/
/-- a `List Unit` related to its length: `[]` to `0`, `() :: l` to `n+1`. -/
@[trocq] inductive RLUN : List Unit → Nat → Type
  | nil : RLUN [] Nat.zero
  | cons {l n} (r : RLUN l n) : RLUN (() :: l) n.succ

/-- `RLUN` is a subsingleton (needed for the `(4,4)` coherence). -/
theorem RLUN.allEq : {l : List Unit} → {n : Nat} → (x y : RLUN l n) → x = y
  | _, _, .nil,    .nil     => rfl
  | _, _, .cons r, .cons r' => by rw [RLUN.allEq r r']

/-- the forward direction: every list is related to its own length. -/
def RLUN.ofLength : (l : List Unit) → RLUN l l.length
  | []      => .nil
  | () :: t => .cons (RLUN.ofLength t)

/-- `n` copies of `()` are related to `n`. -/
def RLUN.ofReplicate : (n : Nat) → RLUN (List.replicate n ()) n
  | 0     => .nil
  | n + 1 => .cons (RLUN.ofReplicate n)

/-- relatedness pins the length. -/
theorem RLUN.toLength : {l : List Unit} → {n : Nat} → RLUN l n → l.length = n
  | _, _, .nil    => rfl
  | _, _, .cons r => by rw [List.length_cons, RLUN.toLength r]

/-- every `List Unit` is `replicate` of its own length (all elements are `()`), the section round-trip. -/
theorem replicate_length_unit : ∀ l : List Unit, List.replicate l.length () = l
  | []      => rfl
  | () :: t => by rw [List.length_cons, List.replicate_succ, replicate_length_unit t]

/- ===================== the ground base `List Unit ≃ Nat`, built over `RLUN` ===================== -/
@[trocq] def RLU : Param map4 map4 (List Unit) Nat where
  R := RLUN
  cov :=
    { map := List.length
      mapInR := fun l _ h => h ▸ RLUN.ofLength l
      rInMap := fun _ _ r => RLUN.toLength r
      rInMapK := fun _ _ r => RLUN.allEq _ r }
  contra :=
    { map := fun n => List.replicate n ()
      mapInR := fun n _ h => h ▸ RLUN.ofReplicate n
      rInMap := fun _ l r => by rw [← RLUN.toLength r, replicate_length_unit]
      rInMapK := fun _ _ r => RLUN.allEq _ r }

/- ===================== worked usage ===================== -/

-- the ground base overrides the diagonal: `⟨List Unit⟩ = Nat`, relation `RLUN` not `PLift (a = b)`.
example : (translate (List Unit)) = Nat := rfl
example : (transfer from (List Unit)).R = RLUN := rfl

-- TYPE-level transport maps (`= List.length` / `= List.replicate · ()`).
example : (transfer from (List Unit)).cov.map [(), ()] = 2 := rfl
example : (transfer from (List Unit)).contra.map 3 = [(), (), ()] := rfl

-- TERM translation of PLAIN list constructors, leaf by leaf (constructors auto-derived from `RLUN`).
example : (translate (List.cons () (List.cons () (@List.nil Unit)))) = 2 := rfl
example : (translate ([(), (), ()] : List Unit)) = 3 := rfl
example : (translate ([] : List Unit)) = 0 := rfl
-- ... and the relatedness (the proof the counterpart is correct).
example : RLUN [(), ()] 2 := relate ([(), ()] : List Unit)
example : RLUN ([] : List Unit) 0 := relate ([] : List Unit)

-- ground type nested under a former: `(List Unit → List Unit)` transfers to `Nat → Nat`, and computes.
example : (transfer from (List Unit → List Unit)).cov.map (fun l => () :: l) 2 = 3 := rfl

-- a goal over `List Unit` transfers to `Nat`.
example : List Unit := by trocq; exact 3

end LeTrocq.Examples
