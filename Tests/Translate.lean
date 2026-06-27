/- The native parametricity translation: `translate% t` rebuilds a term over `B` (here `Unary`). -/
import Lean
import Trocq.Translate
import Examples.NatUnary
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

end Trocq.Tests
