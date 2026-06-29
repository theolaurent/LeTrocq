/- The user surface: the `transfer%` term elaborator and the `trocq` tactic. -/
import Lean
import Trocq.Tactic
import Examples.NatUnary
import Examples.DepParam
namespace Trocq.Tests
open Trocq MapClass Trocq.Std Trocq.Examples

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

/- PARAMETERIZED TYPES in the tactic: `transfer% (List Nat)` lifts the base `Nat ≃ Unary` through the
   `paramListR` relator. The witness's forward map is `List.map` over the base map — and it COMPUTES. -/
example : (transfer% (List Nat)).cov.map [Nat.zero, Nat.succ Nat.zero] = [Unary.z, Unary.s Unary.z] := rfl
/- a `List`-valued function type transfers: the codomain `List Nat` goes through the same relator. -/
example : (transfer% (Nat → List Nat)).cov.map (fun n => [n]) Unary.z = [Unary.z] := rfl
/- nested formers compose: `Option (List Nat)` chains `paramOptionR` over `paramListR` over the base. -/
example : (transfer% (Option (List Nat))).cov.map (some [Nat.zero]) = some [Unary.z] := rfl

/- DEPENDENT Π over a PARAMETERIZED-TYPE binder: `∀ l : List Unary, P l`. The driver now builds the domain
   witness (`paramListR` over the base) for ANY domain type, not just a bare base — the bound variable `l`
   flows into the body's `app` node as a term argument whose relatedness is that domain witness. -/
def AllTriv  (_l : List Unary) : Prop := True
def AllTriv' (_l : List Nat)   : Prop := True
@[trocq] def AllTrivR (l : List Unary) (n : List Nat) (_ : (paramListR Unary Nat RNsym).R l n) :
    Param map1 map1 (AllTriv l) (AllTriv' n) where
  R := fun _ _ => PLift True
  cov    := { map := fun _ => trivial }
  contra := { map := fun _ => trivial }

example : ∀ l : List Unary, AllTriv l := by
  trocq                       -- ⊢ ∀ l : List Nat, AllTriv' l   (binder typed `List Unary`, domain built via relator)
  exact fun _ => trivial

/- DEPENDENT type formers: the relator framework now handles a type FAMILY argument (`Sigma`'s `β`), built as
   a FAMILY of `Param`s. `transfer% (Σ _ : Nat, Nat)` lifts the base through `paramSigmaR`; the forward map (a
   dependent-pair map) COMPUTES. -/
example :
    (transfer% (Σ _ : Nat, Nat)).cov.map ⟨Nat.zero, Nat.succ Nat.zero⟩ = ⟨Unary.z, Unary.s Unary.z⟩ := rfl

/- and a `Prop` goal binding a `Σ`-typed variable transfers — the dependent-Π domain `Σ _ : Unary, Unary` is
   built via `paramSigmaR` (the family machinery feeding the generalized `piTerm`). -/
def SigTriv  (_s : Σ _ : Unary, Unary) : Prop := True
def SigTriv' (_s : Σ _ : Nat, Nat)     : Prop := True
@[trocq] def SigTrivR (s : Σ _ : Unary, Unary) (t : Σ _ : Nat, Nat)
    (_ : (paramSigmaR Unary Nat RNsym (fun _ => Unary) (fun _ => Nat) (fun _ _ _ => RNsym)).R s t) :
    Param map1 map1 (SigTriv s) (SigTriv' t) where
  R := fun _ _ => PLift True
  cov    := { map := fun _ => trivial }
  contra := { map := fun _ => trivial }

example : ∀ s : Σ _ : Unary, Unary, SigTriv s := by
  trocq                       -- ⊢ ∀ s : Σ _ : Nat, Nat, SigTriv' s   (Σ-typed binder, domain via `paramSigmaR`)
  exact fun _ => trivial

/- W-types in the tactic too: a goal binding a `WTree`-typed variable transfers, its domain built via the
   recursive `paramWTreeR` (again the family machinery feeding `piTerm`). -/
def WTriv  (_t : WTree Unary (fun _ => Unary)) : Prop := True
def WTriv' (_t : WTree Nat (fun _ => Nat))     : Prop := True
@[trocq] def WTrivR (s : WTree Unary (fun _ => Unary)) (t : WTree Nat (fun _ => Nat))
    (_ : (paramWTreeR Unary Nat RNsym (fun _ => Unary) (fun _ => Nat) (fun _ _ _ => RNsym)).R s t) :
    Param map1 map1 (WTriv s) (WTriv' t) where
  R := fun _ _ => PLift True
  cov    := { map := fun _ => trivial }
  contra := { map := fun _ => trivial }

example : ∀ t : WTree Unary (fun _ => Unary), WTriv t := by
  trocq                       -- ⊢ ∀ t : WTree Nat (fun _ => Nat), WTriv' t   (W-typed binder, domain via `paramWTreeR`)
  exact fun _ => trivial

/- QUOTIENTS in the tactic: `Quot r` is a former over a type AND a relation (the relation is a term arg). The
   `(4,4)` relator `paramQuotR` builds `Quot r ≃ Quot r'` (maps are `Quot.lift`s); the forward map COMPUTES on
   a concrete class. -/
example : (transfer% (Quot (fun _ _ : Nat => True))).cov.map (Quot.mk _ (Nat.succ Nat.zero))
    = Quot.mk (fun _ _ : Unary => True) (Unary.s Unary.z) := rfl

/- NON-ADJACENT family domain: `Tw Nat Unary β` puts a phantom `C := Unary` between the family's domain
   `A := Nat` and `β`. The driver reads `β`'s domain off its binder type (the `Nat` arg), NOT the preceding
   type arg (`Unary`), so it feeds `β` the `Nat ≃ Unary` witness — and the dependent map still COMPUTES.
   (Were the domain taken as "the preceding type arg", `β : Nat → Type` would wrongly get the `Unary` base.) -/
example :
    (transfer% (Tw Nat Unary (fun _ : Nat => Nat))).cov.map ⟨Nat.zero, Nat.succ Nat.zero⟩
      = ⟨Unary.z, Unary.s Unary.z⟩ := rfl

end Trocq.Tests
