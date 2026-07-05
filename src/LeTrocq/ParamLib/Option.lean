/-
The LeTrocq STANDARD LIBRARY: `Option`.

The same recipe as `List` (see `LeTrocq.ParamLib.List`), smaller — one constructor pair, no recursion. `OptionR` is
the inductive parametricity relation (a TYPE FORMER), `OptionNoneR`/`OptionSomeR` are the constructor TERM
primitives, and `paramOptionRG` is the GRADED relator for the solver/tactic path (variance parallel to `List`).
-/
import LeTrocq.Attr
namespace LeTrocq.ParamLib
open LeTrocq MapClass

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

/- ===================== the GRADED relator (variance mechanism, parallel to `List`) =====================
   `Option` is a COVARIANT functor, so — exactly like `List` — its variance is the identity: the element is
   needed at the demanded output class. Same shape as `paramListRG`, `cases` in place of `induction`. -/

/-- per-map-class minimal element class for `Option` (pure covariance). Parallel to `mapListVariance`. -/
def mapOptionVariance : MapClass → ParamClass
  | map0  => (map0,  map0)
  | map1  => (map1,  map0)
  | map2a => (map2a, map0)
  | map2b => (map2b, map0)
  | map3  => (map3,  map0)
  | map4  => (map4,  map0)

/-- minimal element class to build `Option` at output class `c` (identity — covariant). -/
def optionVariance (c : ParamClass) : ParamClass :=
  ParamClass.join (mapOptionVariance c.1) (ParamClass.negate (mapOptionVariance c.2))

/-- the covariant half `MapHas m (OptionR R)` from the element at `mapOptionVariance m`. -/
def optionCov {A B : Type} :
    (m : MapClass) → (pa : Param (mapOptionVariance m).1 (mapOptionVariance m).2 A B) →
    MapHas m (OptionR A B pa.R)
  | map0,  _  => {}
  | map1,  pa => { map := Option.map pa.cov.map }
  | map2a, pa =>
      { map := Option.map pa.cov.map
        map_in_R := fun oa ob h => by subst h; cases oa with
          | none => exact .none
          | some a => exact .some (pa.cov.map_in_R a _ rfl) }
  | map2b, pa =>
      { map := Option.map pa.cov.map
        R_in_map := fun _ _ r => by cases r with
          | none => rfl
          | some aR => exact congrArg some (pa.cov.R_in_map _ _ aR) }
  | map3,  pa =>
      { map := Option.map pa.cov.map
        map_in_R := fun oa ob h => by subst h; cases oa with
          | none => exact .none
          | some a => exact .some (pa.cov.map_in_R a _ rfl)
        R_in_map := fun _ _ r => by cases r with
          | none => rfl
          | some aR => exact congrArg some (pa.cov.R_in_map _ _ aR) }
  | map4,  pa =>
      { map := Option.map pa.cov.map
        map_in_R := fun oa ob h => by subst h; cases oa with
          | none => exact .none
          | some a => exact .some (pa.cov.map_in_R a _ rfl)
        R_in_map := fun _ _ r => by cases r with
          | none => rfl
          | some aR => exact congrArg some (pa.cov.R_in_map _ _ aR)
        R_in_mapK := fun _ _ _ => OptionR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq) _ _ }

/-- the contravariant half `MapHas n (flip (OptionR R))` from the element's contra at `mapOptionVariance n`. -/
def optionContra {A B : Type} :
    (n : MapClass) → (pa : Param (mapOptionVariance n).2 (mapOptionVariance n).1 A B) →
    MapHas n (fun (ob : Option B) (oa : Option A) => OptionR A B pa.R oa ob)
  | map0,  _  => {}
  | map1,  pa => { map := Option.map pa.contra.map }
  | map2a, pa =>
      { map := Option.map pa.contra.map
        map_in_R := fun ob oa h => by subst h; cases ob with
          | none => exact .none
          | some b => exact .some (pa.contra.map_in_R b _ rfl) }
  | map2b, pa =>
      { map := Option.map pa.contra.map
        R_in_map := fun _ _ r => by cases r with
          | none => rfl
          | some aR => exact congrArg some (pa.contra.R_in_map _ _ aR) }
  | map3,  pa =>
      { map := Option.map pa.contra.map
        map_in_R := fun ob oa h => by subst h; cases ob with
          | none => exact .none
          | some b => exact .some (pa.contra.map_in_R b _ rfl)
        R_in_map := fun _ _ r => by cases r with
          | none => rfl
          | some aR => exact congrArg some (pa.contra.R_in_map _ _ aR) }
  | map4,  pa =>
      { map := Option.map pa.contra.map
        map_in_R := fun ob oa h => by subst h; cases ob with
          | none => exact .none
          | some b => exact .some (pa.contra.map_in_R b _ rfl)
        R_in_map := fun _ _ r => by cases r with
          | none => rfl
          | some aR => exact congrArg some (pa.contra.R_in_map _ _ aR)
        R_in_mapK := fun _ _ _ => OptionR.allEq (fun a a' => (pa.contra.subsingleton a' a).allEq) _ _ }

/-- `Option A ≃ Option B` at ANY output class `(m,n)`, element at the `optionVariance`-minimal class. -/
@[trocq] noncomputable def paramOptionRG (m n : MapClass) (A B : Type)
    (pa : Param (optionVariance (m, n)).1 (optionVariance (m, n)).2 A B) :
    Param m n (Option A) (Option B) where
  R := OptionR A B pa.R
  cov := optionCov m (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := optionContra n (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

end LeTrocq.ParamLib
