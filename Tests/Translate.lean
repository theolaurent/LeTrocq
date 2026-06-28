/- The native parametricity translation: `translate% t` rebuilds a term over `B` (here `Unary`). -/
import Lean
import Trocq.Translate
import Examples.NatUnary
import Examples.ListParam
import Examples.DepParam
namespace Trocq.Tests
open Trocq Trocq.Translate Trocq.Examples

/- `fun n => n.succ.succ` over `Nat` ⤳ the NATIVE `fun u => u.s.s` over `Unary` (not iso-conjugation). -/
example : (translate% (fun n : Nat => Nat.succ (Nat.succ n))) Unary.z = Unary.s (Unary.s Unary.z) := rfl
example : (translate% (fun n : Nat => Nat.succ n)) (Unary.s Unary.z) = Unary.s (Unary.s Unary.z) := rfl
/- a constant is translated too: `Nat.zero` ⤳ `Unary.z`. -/
example : (translate% (Nat.succ Nat.zero)) = Unary.s Unary.z := rfl

/- STRUCTURAL: an unregistered constant is unfolded and translated through its definition.
   `double` bottoms out only at the registered primitives `Nat.succ`/`Nat.zero`. -/
def double (n : Nat) : Nat := Nat.succ (Nat.succ n)
example : (translate% double) Unary.z = Unary.s (Unary.s Unary.z) := rfl

/- `relate%` exposes the RELATEDNESS — the proof that the native term really is the counterpart.
   Here: `(fun n => n.succ)` relates to the native `(fun u => u.s)` under the base relation `RNU`. -/
example : RArrow RNU RNU (fun n : Nat => Nat.succ n) (fun u : Unary => Unary.s u) :=
  relate% (fun n : Nat => Nat.succ n)

/- Nat NUMERAL leaves: a literal `(2 : Nat)` (an `OfNat.ofNat` numeral) is expanded to its `succ`/`zero`
   normal form and translated to the native `Unary` numeral — and it computes. -/
example : (translate% (2 : Nat)) = Unary.s (Unary.s Unary.z) := rfl
/- a numeral nested under a registered primitive translates too. -/
example : (translate% (Nat.succ (1 : Nat))) = Unary.s (Unary.s Unary.z) := rfl
/- `relate%` on a numeral gives the relatedness (the native numeral really is its counterpart). -/
example : RNU (2 : Nat) (Unary.s (Unary.s Unary.z)) := relate% (2 : Nat)

/- POLYMORPHISM: the translation handles `Sort`-binders, so a polymorphic term translates structurally.
   `fun (A : Type) (a : A) => a` ⤳ the native polymorphic identity (its action on `Unary` computes). -/
example : (translate% (fun (A : Type) (a : A) => a)) Unary (Unary.s Unary.z) = Unary.s Unary.z := rfl
/- and the `const`-applied form transports its argument: `fun (A:Type)(f:A→A)(a:A) => f (f a)`. -/
example :
    (translate% (fun (A : Type) (f : A → A) (a : A) => f (f a))) Unary Unary.s Unary.z
      = Unary.s (Unary.s Unary.z) := rfl

/- RECURSORS: a function defined by recursion on `Nat` (via `Nat.rec`) transports to NATIVE `Unary` recursion.
   The registered recursor primitive `NatRecR` lets the translation cross `Nat.rec ↦ Unary.rec`; the motive
   `fun _ => Nat` is itself transported (to `fun _ => Unary`) since `param` routes type-valued terms through
   the type translation. The native `Unary`-recursive function then COMPUTES. -/
def natDouble (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => ih.succ.succ) n
example : (translate% natDouble) Unary.z = Unary.z := rfl
example : (translate% natDouble) (Unary.s Unary.z) = Unary.s (Unary.s Unary.z) := rfl
example : (translate% natDouble) (Unary.s (Unary.s Unary.z)) = Unary.s (Unary.s (Unary.s (Unary.s Unary.z))) := rfl

/- NON-RECURSIVE `match`: a `match`-defined function compiles to an auto-generated matcher (built on
   `Nat.casesOn`, which unfolds to the registered `Nat.rec`); the matcher's dummy `PUnit` argument is handled
   by a built-in trivial relation, so the whole thing transports to native `Unary` code and computes. -/
def natPred : Nat → Nat
  | 0 => 0
  | n + 1 => n
example : (translate% natPred) Unary.z = Unary.z := rfl
example : (translate% natPred) (Unary.s Unary.z) = Unary.z := rfl
example : (translate% natPred) (Unary.s (Unary.s Unary.z)) = Unary.s Unary.z := rfl

/- PARAMETERIZED TYPES: a `List Nat` rebuilds element-by-element as a `List Unary` (the type former `List`
   crosses via `ListR`, the constructors `nil`/`cons` are term primitives, the element numerals expand). -/
example : (translate% ([1, 2] : List Nat)) = [Unary.s Unary.z, Unary.s (Unary.s Unary.z)] := rfl
example : (translate% (List.cons (1 : Nat) [])) = [Unary.s Unary.z] := rfl
example : (translate% ([] : List Nat)) = ([] : List Unary) := rfl
/- a function over lists transports: `List.cons` applied under a λ rebuilds over `Unary`. -/
example : (translate% (fun n : Nat => [n, Nat.succ n])) (Unary.s Unary.z)
    = [Unary.s Unary.z, Unary.s (Unary.s Unary.z)] := rfl
/- `relate%` gives the relatedness: the native list really is the `ListR`-counterpart (an inductive proof,
   `ListR.cons` of the element relatednesses). -/
example : ListR Nat Unary RNU [1, 2] [Unary.s Unary.z, Unary.s (Unary.s Unary.z)] :=
  relate% ([1, 2] : List Nat)
/- `Option` transports the same way. -/
example : (translate% (some (2 : Nat))) = some (Unary.s (Unary.s Unary.z)) := rfl
example : (translate% (none : Option Nat)) = (none : Option Unary) := rfl

/- DEPENDENT parameterized types. `Sigma` (the dependent pair): `⟨1, 2⟩ : Σ _ : Nat, Nat` rebuilds as a pair
   over `Unary` — the type family `fun _ => Nat` is itself transported (to `fun _ => Unary`) and the two
   components cross as terms. -/
example : (translate% (⟨1, 2⟩ : Σ _ : Nat, Nat))
    = (⟨Unary.s Unary.z, Unary.s (Unary.s Unary.z)⟩ : Σ _ : Unary, Unary) := rfl
/- `relate%` gives the `SigmaR` witness (the family relation `RB` is what `param` derived for `fun _ => Nat`).-/
example : SigmaR Nat Unary RNU (fun _ => Nat) (fun _ => Unary) (fun _ _ _ => RNU)
    ⟨1, 2⟩ ⟨Unary.s Unary.z, Unary.s (Unary.s Unary.z)⟩ := relate% (⟨1, 2⟩ : Σ _ : Nat, Nat)

/- W-type: a closed tree needs an empty child type (none is registered over `Nat ≃ Unary`), but the driver
   still crosses `WTree.mk` and the dependent family in BOTH type-former position (the binder `f`'s type) and
   constructor position — exercised here by transporting a closed λ that builds a node. -/
example : (translate% (fun (a : Nat) (f : Nat → WTree Nat (fun _ => Nat)) => @WTree.mk Nat (fun _ => Nat) a f))
    = (fun (a : Unary) (f : Unary → WTree Unary (fun _ => Unary)) => @WTree.mk Unary (fun _ => Unary) a f) := rfl

end Trocq.Tests
