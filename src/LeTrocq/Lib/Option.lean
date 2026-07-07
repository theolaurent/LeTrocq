/-
The LeTrocq STANDARD LIBRARY: `Option`.

The same recipe as `List` (see `LeTrocq.Lib.List`), smaller — one constructor pair, no recursion. `OptionR` is
the inductive parametricity relation (a TYPE FORMER); its constructors auto-register as the `Option.none`/
`Option.some` TERM primitives, and `paramOption` is the GRADED relator for the tactic path (variance like `List`).
-/
import LeTrocq.Driver.Registry
namespace LeTrocq.Lib
open LeTrocq MapClass

@[trocq] inductive OptionR (A A' : Type) (R : A → A' → Type) : Option A → Option A' → Type
  | none : OptionR A A' R none none
  | some {a a'} (aRel : R a a') : OptionR A A' R (some a) (some a')

theorem OptionR.allEq {A A' : Type} {R : A → A' → Type} (hR : ∀ a a' (x y : R a a'), x = y) :
    {oa : Option A} → {ob : Option A'} → (x y : OptionR A A' R oa ob) → x = y
  | _, _, .none,    .none     => rfl
  | _, _, .some aRel, .some aRel' => by rw [hR _ _ aRel aRel']

/- `OptionR.none`/`OptionR.some` auto-register as the `Option.none`/`Option.some` term primitives (tagging
   `OptionR` derives them via `Registry.deriveConstructorPrim`) — no hand-written proxy. -/

/- ===================== the GRADED relator (variance mechanism, parallel to `List`) =====================
   `Option` is a COVARIANT functor, so — exactly like `List` — its variance is the identity: the element is
   needed at the demanded output class. Same shape as `paramList`, `cases` in place of `induction`. -/

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

/-- lifted soundness/completeness for `OptionR`, shared across the `optionCov` arms (cov + its `contra`
    mirror, which swaps the map direction). Non-recursive, so these stay computable. -/
def optionMapInR {A B : Type} {R : A → B → Type} (f : A → B) (fInR : ∀ a b, f a = b → R a b) :
    ∀ oa ob, Option.map f oa = ob → OptionR A B R oa ob :=
  fun oa ob h => by subst h; cases oa with
    | none => exact .none
    | some a => exact .some (fInR a _ rfl)

theorem optionRInMap {A B : Type} {R : A → B → Type} (f : A → B) (fRInMap : ∀ a b, R a b → f a = b) :
    ∀ oa ob, OptionR A B R oa ob → Option.map f oa = ob :=
  fun _ _ r => by cases r with
    | none => rfl
    | some aRel => exact congrArg some (fRInMap _ _ aRel)

def optionContraMapInR {A B : Type} {R : A → B → Type} (g : B → A) (gInR : ∀ b a, g b = a → R a b) :
    ∀ ob oa, Option.map g ob = oa → OptionR A B R oa ob :=
  fun ob oa h => by subst h; cases ob with
    | none => exact .none
    | some b => exact .some (gInR b _ rfl)

theorem optionContraRInMap {A B : Type} {R : A → B → Type} (g : B → A) (gRInMap : ∀ b a, R a b → g b = a) :
    ∀ ob oa, OptionR A B R oa ob → Option.map g ob = oa :=
  fun _ _ r => by cases r with
    | none => rfl
    | some aRel => exact congrArg some (gRInMap _ _ aRel)

/-- the covariant half `MapHas m (OptionR R)` from the element at `mapOptionVariance m`. -/
def optionCov {A B : Type} :
    (m : MapClass) → (pa : Param (mapOptionVariance m).1 (mapOptionVariance m).2 A B) →
    MapHas m (OptionR A B pa.R)
  | map0,  _  => {}
  | map1,  pa => { map := Option.map pa.cov.map }
  | map2a, pa => { map := Option.map pa.cov.map, mapInR := optionMapInR pa.cov.map pa.cov.mapInR }
  | map2b, pa => { map := Option.map pa.cov.map, rInMap := optionRInMap pa.cov.map pa.cov.rInMap }
  | map3,  pa => { map := Option.map pa.cov.map, mapInR := optionMapInR pa.cov.map pa.cov.mapInR,
                   rInMap := optionRInMap pa.cov.map pa.cov.rInMap }
  | map4,  pa => { map := Option.map pa.cov.map, mapInR := optionMapInR pa.cov.map pa.cov.mapInR,
                   rInMap := optionRInMap pa.cov.map pa.cov.rInMap,
                   rInMapK := fun _ _ _ => OptionR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq) _ _ }

/-- the contravariant half `MapHas n (flip (OptionR R))` from the element's contra at `mapOptionVariance n`. -/
def optionContra {A B : Type} :
    (n : MapClass) → (pa : Param (mapOptionVariance n).2 (mapOptionVariance n).1 A B) →
    MapHas n (fun (ob : Option B) (oa : Option A) => OptionR A B pa.R oa ob)
  | map0,  _  => {}
  | map1,  pa => { map := Option.map pa.contra.map }
  | map2a, pa => { map := Option.map pa.contra.map, mapInR := optionContraMapInR pa.contra.map pa.contra.mapInR }
  | map2b, pa => { map := Option.map pa.contra.map, rInMap := optionContraRInMap pa.contra.map pa.contra.rInMap }
  | map3,  pa => { map := Option.map pa.contra.map, mapInR := optionContraMapInR pa.contra.map pa.contra.mapInR,
                   rInMap := optionContraRInMap pa.contra.map pa.contra.rInMap }
  | map4,  pa => { map := Option.map pa.contra.map, mapInR := optionContraMapInR pa.contra.map pa.contra.mapInR,
                   rInMap := optionContraRInMap pa.contra.map pa.contra.rInMap,
                   rInMapK := fun _ _ _ => OptionR.allEq (fun a a' => (pa.contra.subsingleton a' a).allEq) _ _ }

/-- `Option A ≃ Option B` at ANY output class `(m,n)`, element at the `optionVariance`-minimal class. -/
@[trocq] noncomputable def paramOption (m n : MapClass) (A B : Type)
    (pa : Param (optionVariance (m, n)).1 (optionVariance (m, n)).2 A B) :
    Param m n (Option A) (Option B) where
  R := OptionR A B pa.R
  cov := optionCov m (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := optionContra n (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

end LeTrocq.Lib
