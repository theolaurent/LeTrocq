/-
The LeTrocq STANDARD LIBRARY: `Nat`.

The reflexive (DIAGONAL) registration of `Nat`, in the same inductive-relation style as `List`: `NatR` is the
parametricity relation (`0 ~ 0`, and `n+1 ~ m+1` when `n ~ m`), `NatZeroR`/`NatSuccR` the constructor TERM
primitives, `paramNatR` the `(4,4)` relator. This is the LIBRARY DEFAULT — "`Nat` transfers to itself".

It is OVERRIDABLE: a user who registers a different equivalence for `Nat` (e.g. `Nat ≃ Unary` in
`Examples/NatUnary`) shadows this one, because registrations are keyed by head and a later (downstream)
registration wins. So importing both the library and such a user file transfers `Nat` to the user's target,
not to itself — the diagonal here is only the fallback when no other `Nat` equivalence is in scope.
-/
import LeTrocq.Attr
namespace LeTrocq.ParamLib
open LeTrocq MapClass

/-- the parametricity relation of `Nat`: the diagonal. No parameters, so `@[trocq]` classifies it as the
    `Nat` type former (its two indices are the related objects). The constructors are written with
    `Nat.zero`/`Nat.succ` literally (NOT `0`/`+ 1`, which would elaborate to `OfNat`/`HAdd` heads) — those are
    the heads the term primitives must key on, and the numeral leaf in the translation expands to them. -/
@[trocq] inductive NatR : Nat → Nat → Type
  | zero : NatR Nat.zero Nat.zero
  | succ {n n'} (nR : NatR n n') : NatR (Nat.succ n) (Nat.succ n')

theorem NatR.allEq : {a b : Nat} → (x y : NatR a b) → x = y
  | _, _, .zero,    .zero     => rfl
  | _, _, .succ nR, .succ nR' => by rw [NatR.allEq nR nR']

/-- the two constructors as TERM primitives. `Nat.succ` takes one argument, so its witness is one triple. -/
@[trocq] def NatZeroR : NatR Nat.zero Nat.zero := .zero
@[trocq] def NatSuccR (n n' : Nat) (nR : NatR n n') : NatR (Nat.succ n) (Nat.succ n') := .succ nR

/-- `Nat ≃ Nat` at the top class: the identity, completeness by induction on the relation, coherence free
    from `NatR.allEq`. -/
@[trocq] noncomputable def paramNatR : Param map4 map4 Nat Nat where
  R := NatR
  cov :=
    { map := id
      map_in_R := fun a _ h => by subst h; induction a with
        | zero => exact .zero
        | succ _ ih => exact .succ ih
      R_in_map := fun _ _ r => by induction r with
        | zero => rfl
        | succ _ ih => exact congrArg Nat.succ ih
      R_in_mapK := fun _ _ _ => NatR.allEq _ _ }
  contra :=
    { map := id
      map_in_R := fun a _ h => by subst h; induction a with
        | zero => exact .zero
        | succ _ ih => exact .succ ih
      R_in_map := fun _ _ r => by induction r with
        | zero => rfl
        | succ _ ih => exact congrArg Nat.succ ih
      R_in_mapK := fun _ _ _ => NatR.allEq _ _ }

end LeTrocq.ParamLib
