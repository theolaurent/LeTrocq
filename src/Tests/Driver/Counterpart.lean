/- The counterpart translation: `translate t` rebuilds a term over `B` (here `Unary`). -/
import Lean
import LeTrocq.Driver.Tactic
import Examples.NatUnary
import Examples.WTree
namespace LeTrocq.Tests
open LeTrocq LeTrocq.Counterpart LeTrocq.Lib LeTrocq.Examples

/- `fun n => n.succ.succ` over `Nat` ⤳ the native `fun u => u.s.s` over `Unary` (not iso-conjugation). -/
example : (translate (fun n : Nat => Nat.succ (Nat.succ n))) Unary.z = Unary.s (Unary.s Unary.z) := rfl
example : (translate (fun n : Nat => Nat.succ n)) (Unary.s Unary.z) = Unary.s (Unary.s Unary.z) := rfl
/- a constant is translated too: `Nat.zero` ⤳ `Unary.z`. -/
example : (translate (Nat.succ Nat.zero)) = Unary.s Unary.z := rfl

/- `relate` exposes the relatedness — the proof that the native term really is the counterpart. Here
   `(fun n => n.succ)` relates to `(fun u => u.s)` under the base relation `RNU`. -/
example : RArrow RNU RNU (fun n : Nat => Nat.succ n) (fun u : Unary => Unary.s u) :=
  relate (fun n : Nat => Nat.succ n)

/- Nat NUMERAL leaves: a literal `(2 : Nat)` is expanded to `succ`/`zero` normal form and translated to the
   native `Unary` numeral — and it computes. -/
example : (translate (2 : Nat)) = Unary.s (Unary.s Unary.z) := rfl
/- a numeral nested under a registered primitive translates too. -/
example : (translate (Nat.succ (1 : Nat))) = Unary.s (Unary.s Unary.z) := rfl
/- `relate` on a numeral gives the relatedness (the native numeral really is its counterpart). -/
example : RNU (2 : Nat) (Unary.s (Unary.s Unary.z)) := relate (2 : Nat)

/- POLYMORPHISM: the translation handles `Sort`-binders, so a polymorphic term translates structurally.
   `fun (A : Type) (a : A) => a` ⤳ the native polymorphic identity. -/
example : (translate (fun (A : Type) (a : A) => a)) Unary (Unary.s Unary.z) = Unary.s Unary.z := rfl
/- and the `const`-applied form transports its argument: `fun (A:Type)(f:A→A)(a:A) => f (f a)`. -/
example :
    (translate (fun (A : Type) (f : A → A) (a : A) => f (f a))) Unary Unary.s Unary.z
      = Unary.s (Unary.s Unary.z) := rfl

/- PARAMETERIZED TYPES: a `List Nat` rebuilds element-by-element as a `List Unary` (`List` crosses via
   `ListR`, `nil`/`cons` are term primitives, element numerals expand). -/
example : (translate ([1, 2] : List Nat)) = [Unary.s Unary.z, Unary.s (Unary.s Unary.z)] := rfl
example : (translate (List.cons (1 : Nat) [])) = [Unary.s Unary.z] := rfl
example : (translate ([] : List Nat)) = ([] : List Unary) := rfl
/- a function over lists transports: `List.cons` applied under a λ rebuilds over `Unary`. -/
example : (translate (fun n : Nat => [n, Nat.succ n])) (Unary.s Unary.z)
    = [Unary.s Unary.z, Unary.s (Unary.s Unary.z)] := rfl
/- `relate` gives the relatedness: the native list is the `ListR`-counterpart (an inductive proof). -/
example : ListR Nat Unary RNU [1, 2] [Unary.s Unary.z, Unary.s (Unary.s Unary.z)] :=
  relate ([1, 2] : List Nat)
/- `Option` transports the same way. -/
example : (translate (some (2 : Nat))) = some (Unary.s (Unary.s Unary.z)) := rfl
example : (translate (none : Option Nat)) = (none : Option Unary) := rfl

/- DEPENDENT parameterized types. `Sigma`: `⟨1, 2⟩ : Σ _ : Nat, Nat` rebuilds as a pair over `Unary` — the
   family `fun _ => Nat` is itself transported, and the two components cross as terms. -/
example : (translate (⟨1, 2⟩ : Σ _ : Nat, Nat))
    = (⟨Unary.s Unary.z, Unary.s (Unary.s Unary.z)⟩ : Σ _ : Unary, Unary) := rfl
/- `relate` gives the `SigmaR` witness (the family relation derived for `fun _ => Nat`). -/
example : SigmaR Nat Unary RNU (fun _ => Nat) (fun _ => Unary) (fun _ _ _ => RNU)
    ⟨1, 2⟩ ⟨Unary.s Unary.z, Unary.s (Unary.s Unary.z)⟩ := relate (⟨1, 2⟩ : Σ _ : Nat, Nat)

/- W-type: the driver crosses `WTree.mk` and the dependent family in both type-former position (the binder
   `f`'s type) and constructor position — exercised by transporting a closed λ that builds a node. -/
example : (translate (fun (a : Nat) (f : Nat → WTree Nat (fun _ => Nat)) => @WTree.mk Nat (fun _ => Nat) a f))
    = (fun (a : Unary) (f : Unary → WTree Unary (fun _ => Unary)) => @WTree.mk Unary (fun _ => Unary) a f) := rfl

/- PROP-RELATION REFINEMENT: a `Prop`-valued predicate is a relator like any type (counterpart read off the
   relator, relatedness the `PLift (· ↔ ·)` off the `Param`). `translate` rebuilds it; `relate` gives the
   equivalence. -/
def IsTrivN (_ : Nat)   : Prop := True
def IsTrivU (_ : Unary) : Prop := True
@[trocq] def IsTrivR (mc nc : MapClass) (n : Nat) (u : Unary) (_ : RNU n u) :
    Param mc nc (IsTrivN n) (IsTrivU u) := paramPropFromMaps mc nc (fun _ => trivial) (fun _ => trivial)

example : (translate (fun n : Nat => IsTrivN n)) = (fun u : Unary => IsTrivU u) := rfl
/- the relatedness is `PLift (· ↔ ·)`, off the predicate's `Param` witness. -/
example : ∀ (n : Nat) (u : Unary), RNU n u → PLift (IsTrivN n ↔ IsTrivU u) :=
  relate (fun n : Nat => IsTrivN n)
/- connectives are ordinary `@[trocq]` relators, not hardcoded: `⟨And⟩` resolves by registry lookup, and
   `[p n ∧ p n]` projects off the `paramAnd` witness — the same path as any type. -/
example : (translate (fun n : Nat => IsTrivN n ∧ IsTrivN n))
    = (fun u : Unary => IsTrivU u ∧ IsTrivU u) := rfl
example : ∀ (n : Nat) (u : Unary), RNU n u → PLift (IsTrivN n ∧ IsTrivN n ↔ IsTrivU u ∧ IsTrivU u) :=
  relate (fun n : Nat => IsTrivN n ∧ IsTrivN n)

/- QUOTIENTS: `Quot {α} (r : α → α → Prop)` is a former over a type and a relation `r` (a term arg). `Quot.mk
   r a` rebuilds as `Quot.mk r' a'` over `Unary`. -/
example : (translate (Quot.mk (fun _ _ : Nat => True) (2 : Nat)))
    = Quot.mk (fun _ _ : Unary => True) (Unary.s (Unary.s Unary.z)) := rfl

/- CARTESIAN PRODUCT: `(1, 2) : Nat × Nat` rebuilds componentwise over `Unary` (`Prod.mk` is the term
   primitive). -/
example : (translate ((1, 2) : Nat × Nat)) = (Unary.s Unary.z, Unary.s (Unary.s Unary.z)) := rfl
example : ProdR Nat Unary RNU Nat Unary RNU (1, 2) (Unary.s Unary.z, Unary.s (Unary.s Unary.z)) :=
  relate ((1, 2) : Nat × Nat)

/- NON-DEPENDENT SUM: each injection crosses carrying its payload (the other summand's type crosses too). -/
example : (translate (Sum.inl 1 : Nat ⊕ Nat)) = (Sum.inl (Unary.s Unary.z) : Unary ⊕ Unary) := rfl
example : (translate (Sum.inr 2 : Nat ⊕ Nat))
    = (Sum.inr (Unary.s (Unary.s Unary.z)) : Unary ⊕ Unary) := rfl
example : SumR Nat Unary RNU Nat Unary RNU (Sum.inl 1) (Sum.inl (Unary.s Unary.z)) :=
  relate (Sum.inl 1 : Nat ⊕ Nat)

/- ARRAY: an array literal `#[…]` elaborates to `List.toArray […]`, so it crosses through the `List.toArray`
   term primitive — rebuilt element-by-element as the underlying list. -/
example : (translate (#[1, 2] : Array Nat)) = #[Unary.s Unary.z, Unary.s (Unary.s Unary.z)] := rfl
example : (translate (#[] : Array Nat)) = (#[] : Array Unary) := rfl
example : ArrayR Nat Unary RNU #[1, 2] #[Unary.s Unary.z, Unary.s (Unary.s Unary.z)] :=
  relate (#[1, 2] : Array Nat)

/- BOOL has no registered equivalence in scope, so a bool crosses to itself via the whole-diagonal
   short-circuit — its relatedness is `PLift (a = b)` (the generic `paramRefl` relation). -/
example : (translate (fun b : Bool => b)) = (fun b : Bool => b) := rfl
example : (translate (true, false)) = (true, false) := rfl
example : PLift (true = true) := relate true

end LeTrocq.Tests
