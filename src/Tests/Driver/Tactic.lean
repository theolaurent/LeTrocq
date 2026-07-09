/- The user surface: the `transfer` term elaborator and the `trocq` tactic. -/
import Lean
import LeTrocq.Driver.Tactic
import Examples.NatUnary
import Examples.WTree
namespace LeTrocq.Tests
open LeTrocq MapClass LeTrocq.Lib LeTrocq.Examples

/- `transfer` exposes the relatedness witness; its forward map is native function transport over the
   registered `Nat ≃ Unary` base — and it COMPUTES: -/
example : (transfer from (Nat → Nat)).cov.map (· + 1) Unary.z = Unary.s Unary.z := rfl
example : (transfer from (Nat → Nat)).cov.map (fun n => n + 2) Unary.z = Unary.s (Unary.s Unary.z) := rfl
/- the witness relates the two function types by the respectful relation of the base: -/
example : (transfer from (Nat → Nat)).R = RArrow RN.R RN.R := rfl
/- a nested arrow transports too: -/
example : (transfer from (Nat → Nat → Nat)).cov.map (· + ·) Unary.z (Unary.s Unary.z) = Unary.s Unary.z := rfl

/- `Prop` as a leaf type routes through `paramProp` (NOT the `Type` universe combinator, which would stall at
   the `(2a,2a)` ceiling): it reaches the full `(4,4)` — completeness `propext`, coherence free by proof
   irrelevance — so a `Prop`-valued codomain transfers, and the transported predicate COMPUTES. -/
example : (transfer from Prop).R = fun P P' => PLift (P ↔ P') := rfl
example : (transfer from (Nat → Prop)).cov.map (fun n => n = 0) = fun u => Unary.toNat u = 0 := rfl

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
@[trocq] def TrivR (mc nc : MapClass) (u : Unary) (n : Nat) (_ : RNsym.R u n) :
    Param mc nc (Triv u) (Triv' n) := paramPropFromMaps mc nc (fun _ => rfl) (fun _ => rfl)

example : ∀ u : Unary, Triv u := by
  trocq                       -- ⊢ ∀ n : Nat, Triv' n   (resolved via the just-registered `TrivR`)
  exact fun n => rfl

/- MULTI-ARG relators (`app`-of-`app`): a BINARY predicate over two base binders transfers. The driver now
   handles `head x₁ … xₙ` (was single-argument only) — the relator is applied to every binder's triple. -/
def Pos2  (u v : Unary) : Prop := 0 ≤ u.toNat + v.toNat
def Pos2' (m n : Nat)   : Prop := 0 ≤ m + n
@[trocq] def Pos2R (mc nc : MapClass) (u : Unary) (m : Nat) (_ : RNsym.R u m)
    (v : Unary) (n : Nat) (_ : RNsym.R v n) : Param mc nc (Pos2 u v) (Pos2' m n) :=
  paramPropFromMaps mc nc (fun _ => by unfold Pos2'; exact Nat.zero_le _)
                        (fun _ => by unfold Pos2;  exact Nat.zero_le _)

example : ∀ u v : Unary, Pos2 u v := by
  trocq                       -- ⊢ ∀ m n : Nat, Pos2' m n   (two binders + a 2-argument `app` node)
  intro m n; exact Nat.zero_le _

/- REVERSE of a HETEROGENEOUS relator: a goal headed by the relator's B-SIDE head (`Pos'`/`Pos2'`, the `Nat`
   side) now transfers back — `buildConsts` registers the reverse of `PosR`/`Pos2R` under that head (rebuilt by
   `symRelator` as `fun m n <swap> => Param.sym (w n m …)`). Before, this was `constant Pos' not registered`. -/
example : ∀ n : Nat, Pos' n := by
  trocq                       -- ⊢ ∀ u : Unary, Pos u   (reverse `PosR`, keyed under `Pos'`)
  exact fun u => Nat.zero_le u.toNat

example : ∀ m n : Nat, Pos2' m n := by
  trocq                       -- ⊢ ∀ u v : Unary, Pos2 u v   (reverse `Pos2R`, keyed under `Pos2'`)
  intro u v; exact Nat.zero_le _

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
@[trocq] def HOpredR (mc nc : MapClass) (_f : Unary → Unary) (_g : Nat → Nat)
    (_ : RArrow RNsym.R RNsym.R _f _g) : Param mc nc (HOpred _f) (HOpred' _g) :=
  paramPropFromMaps mc nc (fun _ => trivial) (fun _ => trivial)

example : HOpred (fun u : Unary => Unary.s u) := by
  trocq                       -- ⊢ HOpred' (fun n : Nat => Nat.succ n)   (the λ rebuilt over Nat)
  trivial

/- TYPE-VARIABLE arguments: a relator argument that mentions a `∀ A : Type`-bound type variable. The driver
   threads the bound type variable into the term translation (so the λ `fun (a : A) => a` is rebuilt over the
   counterpart type) AND supplies the type's own `Param` witness to the relator — full transport under a
   universe binder. -/
def IdProp {A : Type} (_f : A → A) : Prop := True
@[trocq] def IdPropR (mc nc : MapClass) {A A' : Type} (AR : Param map1 map1 A A')
    (f : A → A) (f' : A' → A') (_ : RArrow AR.R AR.R f f') :
    Param mc nc (IdProp f) (IdProp f') := paramPropFromMaps mc nc (fun _ => trivial) (fun _ => trivial)

example : ∀ A : Type, IdProp (fun (a : A) => a) := by
  trocq                       -- ⊢ ∀ A : Type, IdProp (fun a => a)   (the type var + its λ both transported)
  exact fun _ => trivial

/- COMPOUND type arguments: here the relator's type parameter is `T := A → A` (an arrow over the bound type
   variable), which the solver builds RECURSIVELY — `IsInhabR` then receives that `Param (A → A) (A' → A')`
   as its type witness, and the term λ's relatedness must match the recursively-built arrow relation. -/
def IsInhab {T : Type} (_t : T) : Prop := True
@[trocq] def IsInhabR (mc nc : MapClass) {T T' : Type} (TR : Param map1 map1 T T')
    (t : T) (t' : T') (_ : TR.R t t') : Param mc nc (IsInhab t) (IsInhab t') :=
  paramPropFromMaps mc nc (fun _ => trivial) (fun _ => trivial)

example : ∀ A : Type, IsInhab (fun (a : A) => a) := by
  trocq                       -- ⊢ ∀ A : Type, IsInhab (fun a => a)   (type arg `A → A` built recursively)
  exact fun _ => trivial

/- PARAMETERIZED TYPES in the tactic: `transfer from (List Nat)` lifts the base `Nat ≃ Unary` through the
   `paramList` relator. The witness's forward map is `List.map` over the base map — and it COMPUTES. -/
example : (transfer from (List Nat)).cov.map [Nat.zero, Nat.succ Nat.zero] = [Unary.z, Unary.s Unary.z] := rfl
/- a `List`-valued function type transfers: the codomain `List Nat` goes through the same relator. -/
example : (transfer from (Nat → List Nat)).cov.map (fun n => [n]) Unary.z = [Unary.z] := rfl
/- nested formers compose: `Option (List Nat)` chains `paramOption` over `paramList` over the base. -/
example : (transfer from (Option (List Nat))).cov.map (some [Nat.zero]) = some [Unary.z] := rfl

/- DEPENDENT Π over a PARAMETERIZED-TYPE binder: `∀ l : List Unary, P l`. The driver now builds the domain
   witness (`paramList` over the base) for ANY domain type, not just a bare base — the bound variable `l`
   flows into the body's `app` node as a term argument whose relatedness is that domain witness. -/
def AllTriv  (_l : List Unary) : Prop := True
def AllTriv' (_l : List Nat)   : Prop := True
@[trocq] def AllTrivR (mc nc : MapClass) (l : List Unary) (n : List Nat)
    (_ : ListR Unary Nat RNsym.R l n) : Param mc nc (AllTriv l) (AllTriv' n) :=
  paramPropFromMaps mc nc (fun _ => trivial) (fun _ => trivial)

example : ∀ l : List Unary, AllTriv l := by
  trocq                       -- ⊢ ∀ l : List Nat, AllTriv' l   (binder typed `List Unary`, domain built via relator)
  exact fun _ => trivial

/- DEPENDENT type formers: the relator framework now handles a type FAMILY argument (`Sigma`'s `β`), built as
   a FAMILY of `Param`s. `transfer from (Σ _ : Nat, Nat)` lifts the base through `paramSigma`; the forward map (a
   dependent-pair map) COMPUTES. -/
example :
    (transfer from (Σ _ : Nat, Nat)).cov.map ⟨Nat.zero, Nat.succ Nat.zero⟩ = ⟨Unary.z, Unary.s Unary.z⟩ := rfl

/- and a `Prop` goal binding a `Σ`-typed variable transfers — the dependent-Π domain `Σ _ : Unary, Unary` is
   built via `paramSigma` (the family machinery feeding the generalized `piTerm`). -/
def SigTriv  (_s : Σ _ : Unary, Unary) : Prop := True
def SigTriv' (_s : Σ _ : Nat, Nat)     : Prop := True
@[trocq] def SigTrivR (mc nc : MapClass) (s : Σ _ : Unary, Unary) (t : Σ _ : Nat, Nat)
    (_ : SigmaR Unary Nat RNsym.R (fun _ => Unary) (fun _ => Nat) (fun _ _ _ => RNsym.R) s t) :
    Param mc nc (SigTriv s) (SigTriv' t) := paramPropFromMaps mc nc (fun _ => trivial) (fun _ => trivial)

example : ∀ s : Σ _ : Unary, Unary, SigTriv s := by
  trocq                       -- ⊢ ∀ s : Σ _ : Nat, Nat, SigTriv' s   (Σ-typed binder, domain via `paramSigma`)
  exact fun _ => trivial

/- W-types in the tactic too: a goal binding a `WTree`-typed variable transfers, its domain built via the
   recursive `paramWTree` (again the family machinery feeding `piTerm`). -/
def WTriv  (_t : WTree Unary (fun _ => Unary)) : Prop := True
def WTriv' (_t : WTree Nat (fun _ => Nat))     : Prop := True
@[trocq] def WTrivR (mc nc : MapClass) (s : WTree Unary (fun _ => Unary)) (t : WTree Nat (fun _ => Nat))
    (_ : WTreeR Unary Nat RNsym.R (fun _ => Unary) (fun _ => Nat) (fun _ _ _ => RNsym.R) s t) :
    Param mc nc (WTriv s) (WTriv' t) := paramPropFromMaps mc nc (fun _ => trivial) (fun _ => trivial)

example : ∀ t : WTree Unary (fun _ => Unary), WTriv t := by
  trocq                       -- ⊢ ∀ t : WTree Nat (fun _ => Nat), WTriv' t   (W-typed binder, domain via `paramWTree`)
  exact fun _ => trivial

/- QUOTIENTS in the tactic: `Quot r` is a former over a type AND a relation (the relation is a term arg). The
   graded relator `paramQuot` builds `Quot r ≃ Quot r'` (maps are `Quot.lift`s); the forward map COMPUTES on
   a concrete class. -/
example : (transfer from (Quot (fun _ _ : Nat => True))).cov.map (Quot.mk _ (Nat.succ Nat.zero))
    = Quot.mk (fun _ _ : Unary => True) (Unary.s Unary.z) := rfl

/- CARTESIAN PRODUCT in the tactic: `paramProd` lifts the base through BOTH parameters; its forward map acts
   componentwise — and it COMPUTES. (`Bool` rides along DIAGONALLY in the mixed `Nat × Bool`.) -/
example : (transfer from (Nat × Nat)).cov.map (Nat.zero, Nat.succ Nat.zero) = (Unary.z, Unary.s Unary.z) := rfl
example : (transfer from (Nat × Bool)).cov.map (Nat.zero, true) = (Unary.z, true) := rfl

/- NON-DEPENDENT SUM: `paramSum`'s forward map is `Sum.map` of the two base maps; each injection computes. -/
example : (transfer from (Nat ⊕ Nat)).cov.map (Sum.inl Nat.zero) = (Sum.inl Unary.z : Unary ⊕ Unary) := rfl
example : (transfer from (Nat ⊕ Nat)).cov.map (Sum.inr (Nat.succ Nat.zero))
    = (Sum.inr (Unary.s Unary.z) : Unary ⊕ Unary) := rfl

/- ARRAY: `paramArray` delegates to `paramList` through `toList`; the forward map rebuilds the array. -/
example : (transfer from (Array Nat)).cov.map #[Nat.zero, Nat.succ Nat.zero] = #[Unary.z, Unary.s Unary.z] := rfl

/- BOOL takes the WHOLE-DIAGONAL short-circuit: `Bool`'s counterpart is itself, so `assemble` builds the
   generic `paramRefl` (relation `PLift (a=b)`, identity maps) — no per-type registration. `transfer from (Bool →
   Bool)` transports a function over that diagonal — the forward map is the function itself. -/
example : (transfer from (Bool → Bool)).cov.map (fun b => !b) true = false := rfl

/- EMPTY / UNIT (in `Type`): also unregistered — they take the same whole-diagonal short-circuit (`paramRefl`),
   so they transfer as leaves and compose with the formers. `Empty` has no values; `Unit` rides trivially. -/
example : (transfer from (Option Empty)).cov.map none = none := rfl
example : (transfer from (Nat → Unit)).cov.map (fun _ => Unit.unit) Unary.z = Unit.unit := rfl
example : (transfer from (Nat × Unit)).cov.map (Nat.zero, Unit.unit) = (Unary.z, Unit.unit) := rfl

/- `Tw A C B` carries a phantom type parameter `C` BETWEEN the family's domain `A` and the family `B`, and is
   just `Sigma B`, so its graded relator delegates to the standard library's `paramSigma`. It exists only to
   exercise the driver's non-adjacent-family-domain routing, so it lives here with its test (not in `Examples/`). -/
def Tw (A _C : Type) (B : A → Type) : Type := Sigma B

@[trocq] noncomputable def paramTwR (m n : MapClass) (A A' : Type)
    (pa : Param (sigmaVariance (m, n)).1.1 (sigmaVariance (m, n)).1.2 A A')
    (C C' : Type) (_pc : Param map4 map4 C C') (B : A → Type) (B' : A' → Type)
    (pb : (a : A) → (a' : A') → pa.R a a' →
          Param (sigmaVariance (m, n)).2.1 (sigmaVariance (m, n)).2.2 (B a) (B' a')) :
    Param m n (Tw A C B) (Tw A' C' B') := paramSigma m n A A' pa B B' pb

/- NON-ADJACENT family domain: `Tw Nat Unary β` puts a phantom `C := Unary` between the family's domain
   `A := Nat` and `β`. The driver reads `β`'s domain off its binder type (the `Nat` arg), NOT the preceding
   type arg (`Unary`), so it feeds `β` the `Nat ≃ Unary` witness — and the dependent map still COMPUTES.
   (Were the domain taken as "the preceding type arg", `β : Nat → Type` would wrongly get the `Unary` base.) -/
example :
    (transfer from (Tw Nat Unary (fun _ : Nat => Nat))).cov.map ⟨Nat.zero, Nat.succ Nat.zero⟩
      = ⟨Unary.z, Unary.s Unary.z⟩ := rfl

/- EQUALITY: `paramEq` relates `a = b` to `a' = b'` over a related type (a relator whose first argument
   carries the whole `Param`, not a bare relation). Both surfaces cross `=`: `transfer`/`trocq` (type/goal),
   and — since a proposition is a `Sort 0` type — `relate` (term), whose `[a = b] : PLift (a=b ↔ a'=b')` is
   projected off the `paramEq` witness. -/
example : (transfer from (∀ n : Nat, n = n)).cov.map (fun _ => rfl) = (fun _ : Unary => rfl) := rfl

example : ∀ u : Unary, u = u := by
  trocq                       -- ⊢ ∀ n : Nat, n = n
  exact fun _ => rfl

example : ∀ (n : Nat) (n' : Unary), RN.R n n' → PLift (n = n ↔ n' = n') :=
  relate (fun n : Nat => n = n)

/- CONNECTIVES IN GOALS: `And`/`Or`/`Not`/`Iff` are graded relators (`LeTrocq.Lib.Logic`), so the
   SOLVER path crosses them — a goal headed by a connective transfers, its `Prop` parts each recursing as a
   `Param` component (like `Prod`). Nesting works (`(· ∧ ·) ∨ ¬¬·`). -/
example : ∀ u : Unary, Pos u ∧ Pos u := by
  trocq                       -- ⊢ ∀ n : Nat, Pos' n ∧ Pos' n
  exact fun n => ⟨Nat.zero_le n, Nat.zero_le n⟩

example : ∀ u : Unary, Pos u ∨ Pos u := by
  trocq
  exact fun n => Or.inl (Nat.zero_le n)

example : ∀ u : Unary, (Pos u ∧ Pos u) ∨ ¬ ¬ Pos u := by
  trocq                       -- ⊢ ∀ n : Nat, (Pos' n ∧ Pos' n) ∨ ¬¬ Pos' n
  exact fun n => Or.inl ⟨Nat.zero_le n, Nat.zero_le n⟩

end LeTrocq.Tests
