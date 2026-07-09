/-
`Array` — an `Array α` wraps `List α` (its `toList`), so its parametricity is `List`'s read through `toList`:
everything REUSES `LeTrocq.Lib.List` rather than re-deriving. The conversions are definitional (structure eta,
`(l.toArray).toList` reduces to `l`), so `ArrayR`, the `List.toArray` term primitive `ListToArrayR`, and the
graded `paramArray` all delegate to `List`'s `listCov`/`listContra` on the underlying lists.
-/
import LeTrocq.Lib.List
namespace LeTrocq.Lib
open LeTrocq MapClass

/-- two arrays are related iff their underlying lists are `ListR`-related. A TYPE FORMER keyed by `Array`. -/
@[trocq] def ArrayR (A A' : Type) (R : A → A' → Type) (a : Array A) (b : Array A') : Type :=
  ListR A A' R a.toList b.toList

/-- an array literal `#[…]` is `List.toArray l`; its relatedness is the underlying list's, witnessed by `lRel`
    (the types match since `(l.toArray).toList` reduces to `l`). Keyed by `List.toArray`. -/
@[trocq] def ListToArrayR (A A' : Type) (R : A → A' → Type)
    (l : List A) (l' : List A') (lRel : ListR A A' R l l') :
    ArrayR A A' R l.toArray l'.toArray := lRel

/- ===================== the graded relator (variance parallel to `paramList`) =====================
   `Array` is `List` through `toList`, so it reuses `mapListVariance`/`listVariance` and each graded half
   delegates to `listCov`/`listContra` (`rInMap` re-wraps through structure eta with `congrArg Array.mk`). -/

/-- the covariant half `MapHas m (ArrayR R)`, delegating to `listCov m` on `toList`. -/
noncomputable def arrayCov {A B : Type} :
    (m : MapClass) → (pa : Param (mapListVariance m).1 (mapListVariance m).2 A B) →
    MapHas m (ArrayR A B pa.R)
  | map0,  _  => {}
  | map1,  pa => { map := fun a => ⟨a.toList.map pa.cov.map⟩ }
  | map2a, pa =>
      { map := fun a => ⟨a.toList.map pa.cov.map⟩
        mapInR := fun a _ h => by subst h; exact (listCov map2a pa).mapInR a.toList _ rfl }
  | map2b, pa =>
      { map := fun a => ⟨a.toList.map pa.cov.map⟩
        rInMap := fun a b r => congrArg Array.mk ((listCov map2b pa).rInMap a.toList b.toList r) }
  | map3,  pa =>
      { map := fun a => ⟨a.toList.map pa.cov.map⟩
        mapInR := fun a _ h => by subst h; exact (listCov map3 pa).mapInR a.toList _ rfl
        rInMap := fun a b r => congrArg Array.mk ((listCov map3 pa).rInMap a.toList b.toList r) }
  | map4,  pa =>
      { map := fun a => ⟨a.toList.map pa.cov.map⟩
        mapInR := fun a _ h => by subst h; exact (listCov map4 pa).mapInR a.toList _ rfl
        rInMap := fun a b r => congrArg Array.mk ((listCov map4 pa).rInMap a.toList b.toList r)
        rInMapK := fun _ _ _ => ListR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq) _ _ }

/-- the contravariant half `MapHas n (flip (ArrayR R))`, delegating to `listContra n` on `toList`. -/
noncomputable def arrayContra {A B : Type} :
    (n : MapClass) → (pa : Param (mapListVariance n).2 (mapListVariance n).1 A B) →
    MapHas n (fun (b : Array B) (a : Array A) => ArrayR A B pa.R a b)
  | map0,  _  => {}
  | map1,  pa => { map := fun b => ⟨b.toList.map pa.contra.map⟩ }
  | map2a, pa =>
      { map := fun b => ⟨b.toList.map pa.contra.map⟩
        mapInR := fun b _ h => by subst h; exact (listContra map2a pa).mapInR b.toList _ rfl }
  | map2b, pa =>
      { map := fun b => ⟨b.toList.map pa.contra.map⟩
        rInMap := fun b a r => congrArg Array.mk ((listContra map2b pa).rInMap b.toList a.toList r) }
  | map3,  pa =>
      { map := fun b => ⟨b.toList.map pa.contra.map⟩
        mapInR := fun b _ h => by subst h; exact (listContra map3 pa).mapInR b.toList _ rfl
        rInMap := fun b a r => congrArg Array.mk ((listContra map3 pa).rInMap b.toList a.toList r) }
  | map4,  pa =>
      { map := fun b => ⟨b.toList.map pa.contra.map⟩
        mapInR := fun b _ h => by subst h; exact (listContra map4 pa).mapInR b.toList _ rfl
        rInMap := fun b a r => congrArg Array.mk ((listContra map4 pa).rInMap b.toList a.toList r)
        rInMapK := fun _ _ _ => ListR.allEq (fun a a' => (pa.contra.subsingleton a' a).allEq) _ _ }

/-- `Array A ≃ Array B` at ANY output class `(m,n)`, element at the `listVariance`-minimal class. -/
@[trocq] noncomputable def paramArray (m n : MapClass) (A B : Type)
    (pa : Param (listVariance (m, n)).1 (listVariance (m, n)).2 A B) :
    Param m n (Array A) (Array B) where
  R := ArrayR A B pa.R
  cov := arrayCov m (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := arrayContra n (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

end LeTrocq.Lib
