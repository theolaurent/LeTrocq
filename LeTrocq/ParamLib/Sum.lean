/-
The LeTrocq STANDARD LIBRARY: `Sum` (⊕, the non-dependent disjoint union).

Two type parameters (like `Prod`) but two constructors (like `Option`): `SumR` is the parametricity relation
(`inl ~ inl`, `inr ~ inr`), `SumInlR`/`SumInrR` the constructor TERM primitives, `paramSumR` the `(4,4)`
relator. The forward map is `Sum.map` of the two component maps.
-/
import LeTrocq.Attr
namespace LeTrocq.ParamLib
open LeTrocq MapClass

/-- two sums are related iff they take the same injection with componentwise-related payloads. -/
@[trocq] inductive SumR (A A' : Type) (RA : A → A' → Type) (B B' : Type) (RB : B → B' → Type) :
    A ⊕ B → A' ⊕ B' → Type
  | inl {a a'} (aR : RA a a') : SumR A A' RA B B' RB (.inl a) (.inl a')
  | inr {b b'} (bR : RB b b') : SumR A A' RA B B' RB (.inr b) (.inr b')

theorem SumR.allEq {A A' : Type} {RA : A → A' → Type} {B B' : Type} {RB : B → B' → Type}
    (hA : ∀ a a' (x y : RA a a'), x = y) (hB : ∀ b b' (x y : RB b b'), x = y) :
    {s : A ⊕ B} → {t : A' ⊕ B'} → (x y : SumR A A' RA B B' RB s t) → x = y
  | _, _, .inl aR, .inl aR' => by rw [hA _ _ aR aR']
  | _, _, .inr bR, .inr bR' => by rw [hB _ _ bR bR']

/-- the two constructors as TERM primitives (the OTHER summand's type still crosses, as the unused triple). -/
@[trocq] def SumInlR (A A' : Type) (RA : A → A' → Type) (B B' : Type) (RB : B → B' → Type)
    (a : A) (a' : A') (aR : RA a a') : SumR A A' RA B B' RB (.inl a) (.inl a') := .inl aR
@[trocq] def SumInrR (A A' : Type) (RA : A → A' → Type) (B B' : Type) (RB : B → B' → Type)
    (b : B) (b' : B') (bR : RB b b') : SumR A A' RA B B' RB (.inr b) (.inr b') := .inr bR

/-- `A ⊕ B ≃ A' ⊕ B'` at the top class: maps by `Sum.map`, completeness by casing the relation, coherence
    free from `SumR.allEq`. -/
@[trocq] noncomputable def paramSumR (A A' : Type) (pa : Param map4 map4 A A')
    (B B' : Type) (pb : Param map4 map4 B B') :
    Param map4 map4 (A ⊕ B) (A' ⊕ B') where
  R := SumR A A' pa.R B B' pb.R
  cov :=
    { map := Sum.map pa.cov.map pb.cov.map
      map_in_R := fun s _ h => by subst h; cases s with
        | inl a => exact .inl (pa.cov.map_in_R a _ rfl)
        | inr b => exact .inr (pb.cov.map_in_R b _ rfl)
      R_in_map := fun _ _ r => by cases r with
        | inl aR => exact congrArg Sum.inl (pa.cov.R_in_map _ _ aR)
        | inr bR => exact congrArg Sum.inr (pb.cov.R_in_map _ _ bR)
      R_in_mapK := fun _ _ _ => SumR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq)
        (fun b b' => (pb.cov.subsingleton b b').allEq) _ _ }
  contra :=
    { map := Sum.map pa.contra.map pb.contra.map
      map_in_R := fun t _ h => by subst h; cases t with
        | inl a => exact .inl (pa.contra.map_in_R a _ rfl)
        | inr b => exact .inr (pb.contra.map_in_R b _ rfl)
      R_in_map := fun _ _ r => by cases r with
        | inl aR => exact congrArg Sum.inl (pa.contra.R_in_map _ _ aR)
        | inr bR => exact congrArg Sum.inr (pb.contra.R_in_map _ _ bR)
      R_in_mapK := fun _ _ _ => SumR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq)
        (fun b b' => (pb.cov.subsingleton b b').allEq) _ _ }

end LeTrocq.ParamLib
