/-
The LeTrocq STANDARD LIBRARY: `Array`.

An `Array α` is a structure wrapping `List α` (its `toList`), so its parametricity is `List`'s, read through
`toList`: `ArrayR a b := ListR _ _ _ a.toList b.toList`. The relation and relator REUSE `LeTrocq.ParamLib.List`
rather than re-deriving an inductive — the `Array`/`List` conversions are definitional (`(l.toArray).toList`
reduces to `l`, and `⟨a.toList⟩` is `a` by structure eta), so each field delegates to `paramListR` on the
underlying lists.

  • TYPE FORMER `ArrayR` — so `paramType` can cross `Array a`.
  • TERM primitive `ListToArrayR` keyed by `List.toArray` — an array literal `#[…]` elaborates to
    `List.toArray […]`, so this is the head the native translation actually meets.
  • the `(4,4)` relator `paramArrayR` (for `trocq` / `transfer%`).
-/
import LeTrocq.ParamLib.List
namespace LeTrocq.ParamLib
open LeTrocq MapClass

/-- two arrays are related iff their underlying lists are `ListR`-related. A TYPE FORMER keyed by `Array`. -/
@[trocq] def ArrayR (A A' : Type) (R : A → A' → Type) (a : Array A) (b : Array A') : Type :=
  ListR A A' R a.toList b.toList

/-- an array literal is `List.toArray l`; its relatedness is the underlying list's. Keyed by `List.toArray`
    (homogeneous), the witness is literally `lR` — `(l.toArray).toList` reduces to `l`, so the types match. -/
@[trocq] def ListToArrayR (A A' : Type) (R : A → A' → Type)
    (l : List A) (l' : List A') (lR : ListR A A' R l l') :
    ArrayR A A' R l.toArray l'.toArray := lR

/-- `Array A ≃ Array B` at the top class: each field delegates to `paramListR` on `toList`. The forward map
    builds the array directly from the mapped list (`⟨…⟩`) so `(map a).toList` is `rfl`; `R_in_map` re-wraps
    the list equality through structure eta (`congrArg Array.mk`); coherence is `List`'s `ListR.allEq`. -/
@[trocq] noncomputable def paramArrayR (A B : Type) (pa : Param map4 map4 A B) :
    Param map4 map4 (Array A) (Array B) where
  R := ArrayR A B pa.R
  cov :=
    { map := fun a => ⟨a.toList.map pa.cov.map⟩
      map_in_R := fun a _ h => by subst h; exact (paramListR A B pa).cov.map_in_R a.toList _ rfl
      R_in_map := fun a b r => congrArg Array.mk ((paramListR A B pa).cov.R_in_map a.toList b.toList r)
      R_in_mapK := fun _ _ _ => ListR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq) _ _ }
  contra :=
    { map := fun b => ⟨b.toList.map pa.contra.map⟩
      map_in_R := fun b _ h => by subst h; exact (paramListR A B pa).contra.map_in_R b.toList _ rfl
      R_in_map := fun b a r => congrArg Array.mk ((paramListR A B pa).contra.R_in_map b.toList a.toList r)
      R_in_mapK := fun _ _ _ => ListR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq) _ _ }

end LeTrocq.ParamLib
