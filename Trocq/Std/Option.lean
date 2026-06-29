/-
The Trocq STANDARD LIBRARY: `Option`.

The same recipe as `List` (see `Trocq.Std.List`), smaller — one constructor pair, no recursion. `OptionR` is
the inductive parametricity relation (a TYPE FORMER), `OptionNoneR`/`OptionSomeR` are the constructor TERM
primitives, and `paramOptionR` is the `(4,4)` relator for the solver/tactic path.
-/
import Trocq.Attr
namespace Trocq.Std
open Trocq MapClass

@[trocq] inductive OptionR (A A' : Type) (R : A → A' → Type) : Option A → Option A' → Type
  | none : OptionR A A' R none none
  | some {a a'} (aR : R a a') : OptionR A A' R (some a) (some a')

theorem OptionR.allEq {A A' : Type} {R : A → A' → Type} (hR : ∀ a a' (x y : R a a'), x = y) :
    {oa : Option A} → {ob : Option A'} → (x y : OptionR A A' R oa ob) → x = y
  | _, _, .none,    .none     => rfl
  | _, _, .some aR, .some aR' => by rw [hR _ _ aR aR']

@[trocq] def OptionNoneR (A A' : Type) (R : A → A' → Type) : OptionR A A' R none none := .none
@[trocq] def OptionSomeR (A A' : Type) (R : A → A' → Type) (a : A) (a' : A') (aR : R a a') :
    OptionR A A' R (some a) (some a') := .some aR

@[trocq] noncomputable def paramOptionR (A B : Type) (pa : Param map4 map4 A B) :
    Param map4 map4 (Option A) (Option B) where
  R := OptionR A B pa.R
  cov :=
    { map := Option.map pa.cov.map
      map_in_R := fun oa ob h => by
        subst h; cases oa with
        | none => exact .none
        | some a => exact .some (pa.cov.map_in_R a _ rfl)
      R_in_map := fun _ _ r => by
        cases r with
        | none => rfl
        | some aR => exact congrArg some (pa.cov.R_in_map _ _ aR)
      R_in_mapK := fun _ _ _ => OptionR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq) _ _ }
  contra :=
    { map := Option.map pa.contra.map
      map_in_R := fun ob oa h => by
        subst h; cases ob with
        | none => exact .none
        | some b => exact .some (pa.contra.map_in_R b _ rfl)
      R_in_map := fun _ _ r => by
        cases r with
        | none => rfl
        | some aR => exact congrArg some (pa.contra.R_in_map _ _ aR)
      R_in_mapK := fun _ _ _ => OptionR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq) _ _ }

end Trocq.Std
