/- The user surface: the `transfer%` term elaborator and the `trocq` tactic. -/
import Lean
import Trocq.Tactic
import Examples.NatUnary
namespace Trocq.Tests
open Trocq MapClass Trocq.Examples

/- `transfer%` exposes the relatedness witness; its forward map is native function transport over the
   registered `Nat ≃ Unary` base — and it COMPUTES: -/
example : (transfer% (Nat → Nat)).cov.map (· + 1) Unary.z = Unary.s Unary.z := rfl
example : (transfer% (Nat → Nat)).cov.map (fun n => n + 2) Unary.z = Unary.s (Unary.s Unary.z) := rfl
/- the witness relates the two function types by the respectful relation of the base: -/
example : (transfer% (Nat → Nat)).R = RArrow RN.R RN.R := rfl
/- a nested arrow transports too: -/
example : (transfer% (Nat → Nat → Nat)).cov.map (· + ·) Unary.z (Unary.s Unary.z) = Unary.s Unary.z := rfl

/- `trocq` proves a `Unary`-side goal by transferring it to the (easier) `Nat`-side counterpart. -/
example : Unary → Unary := by
  trocq          -- ⊢ Nat → Nat
  exact (· + 1)
example : Unary → Unary → Unary := by
  trocq          -- ⊢ Nat → Nat → Nat
  exact (· + ·)

/- the PAYOFF: a `Prop`-valued dependent goal. `trocq` recognizes `∀ (x : Base), Pred x` via the generic
   `app` rule (registered constant `Pos`), transfers it to the `Nat`-side, and leaves the easier goal. -/
example : ∀ u : Unary, Pos u := by
  trocq                       -- ⊢ ∀ n : Nat, Pos' n
  exact fun n => Nat.zero_le n

/- NO HARDCODING: a predicate registered with `@[trocq]` RIGHT HERE (not in the library) is picked up by
   `trocq` automatically — the driver reads its registries from the `@[trocq]` env extension. -/
def Triv  (u : Unary) : Prop := u = u
def Triv' (n : Nat)   : Prop := n = n
@[trocq] def TrivR (u : Unary) (n : Nat) (_ : RNsym.R u n) : Param map1 map1 (Triv u) (Triv' n) where
  R := fun _ _ => PLift True
  cov    := { map := fun _ => rfl }
  contra := { map := fun _ => rfl }

example : ∀ u : Unary, Triv u := by
  trocq                       -- ⊢ ∀ n : Nat, Triv' n   (resolved via the just-registered `TrivR`)
  exact fun n => rfl

/- MULTI-ARG relators (`app`-of-`app`): a BINARY predicate over two base binders transfers. The driver now
   handles `head x₁ … xₙ` (was single-argument only) — the relator is applied to every binder's triple. -/
def Pos2  (u v : Unary) : Prop := 0 ≤ u.toNat + v.toNat
def Pos2' (m n : Nat)   : Prop := 0 ≤ m + n
@[trocq] def Pos2R (u : Unary) (m : Nat) (_ : RNsym.R u m) (v : Unary) (n : Nat) (_ : RNsym.R v n) :
    Param map1 map1 (Pos2 u v) (Pos2' m n) where
  R := fun _ _ => PLift True
  cov    := { map := fun _ => by unfold Pos2'; exact Nat.zero_le _ }
  contra := { map := fun _ => by unfold Pos2;  exact Nat.zero_le _ }

example : ∀ u v : Unary, Pos2 u v := by
  trocq                       -- ⊢ ∀ m n : Nat, Pos2' m n   (two binders + a 2-argument `app` node)
  intro m n; exact Nat.zero_le _

/- NESTED arguments: a relator argument is no longer restricted to a bound variable — it can be an
   ARBITRARY term over the base. `Pos (Unary.s u)` transfers: the driver rebuilds the argument `Unary.s u`
   natively as `Nat.succ n` (with relatedness) via the term translation, then applies the relator. -/
example : ∀ u : Unary, Pos (Unary.s u) := by
  trocq                       -- ⊢ ∀ n : Nat, Pos' (Nat.succ n)
  exact fun n => Nat.zero_le _

/- LAMBDA arguments: a higher-order predicate whose argument is a λ. `HOpred (fun u => u.s)` transfers, the
   λ `fun u : Unary => Unary.s u` being rebuilt natively as `fun n : Nat => Nat.succ n` — full transport. -/
def HOpred  (_f : Unary → Unary) : Prop := True
def HOpred' (_g : Nat → Nat)     : Prop := True
@[trocq] def HOpredR (_f : Unary → Unary) (_g : Nat → Nat) (_ : RArrow RNsym.R RNsym.R _f _g) :
    Param map1 map1 (HOpred _f) (HOpred' _g) where
  R := fun _ _ => PLift True
  cov    := { map := fun _ => trivial }
  contra := { map := fun _ => trivial }

example : HOpred (fun u : Unary => Unary.s u) := by
  trocq                       -- ⊢ HOpred' (fun n : Nat => Nat.succ n)   (the λ rebuilt over Nat)
  trivial

/- TYPE-VARIABLE arguments: a relator argument that mentions a `∀ A : Type`-bound type variable. The driver
   threads the bound type variable into the term translation (so the λ `fun (a : A) => a` is rebuilt over the
   counterpart type) AND supplies the type's own `Param` witness to the relator — full transport under a
   universe binder. -/
def IdProp {A : Type} (_f : A → A) : Prop := True
@[trocq] def IdPropR {A A' : Type} (AR : Param map1 map1 A A')
    (f : A → A) (f' : A' → A') (_ : RArrow AR.R AR.R f f') :
    Param map1 map1 (IdProp f) (IdProp f') where
  R := fun _ _ => PLift True
  cov    := { map := fun _ => trivial }
  contra := { map := fun _ => trivial }

example : ∀ A : Type, IdProp (fun (a : A) => a) := by
  trocq                       -- ⊢ ∀ A : Type, IdProp (fun a => a)   (the type var + its λ both transported)
  exact fun _ => trivial

/- COMPOUND type arguments: here the relator's type parameter is `T := A → A` (an arrow over the bound type
   variable), which the solver builds RECURSIVELY — `IsInhabR` then receives that `Param (A → A) (A' → A')`
   as its type witness, and the term λ's relatedness must match the recursively-built arrow relation. -/
def IsInhab {T : Type} (_t : T) : Prop := True
@[trocq] def IsInhabR {T T' : Type} (TR : Param map1 map1 T T')
    (t : T) (t' : T') (_ : TR.R t t') : Param map1 map1 (IsInhab t) (IsInhab t') where
  R := fun _ _ => PLift True
  cov    := { map := fun _ => trivial }
  contra := { map := fun _ => trivial }

example : ∀ A : Type, IsInhab (fun (a : A) => a) := by
  trocq                       -- ⊢ ∀ A : Type, IsInhab (fun a => a)   (type arg `A → A` built recursively)
  exact fun _ => trivial

end Trocq.Tests
