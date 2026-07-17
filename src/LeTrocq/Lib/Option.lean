/-
`Option` — like `List` (see `LeTrocq.Lib.List`) but smaller: one constructor pair, no recursion. `OptionR` is
the inductive parametricity relation (a TYPE FORMER); its constructors auto-register as the `Option.none`/
`Option.some` term primitives; `paramOption` is the graded relator (variance identical to `List`).
-/
import LeTrocq.Driver.Registry
namespace LeTrocq.Lib
open LeTrocq MapClass

/-- two options related constructor-by-constructor: both `none`, or both `some` with `R`-related payloads. -/
@[trocq] inductive OptionR (A A' : Type) (R : A → A' → Type) : Option A → Option A' → Type
  | none : OptionR A A' R none none
  | some {a a'} (aRel : R a a') : OptionR A A' R (some a) (some a')

/-- the relation is a subsingleton whenever the element relation is — needed for the `(4,4)` coherence. -/
theorem OptionR.allEq {A A' : Type} {R : A → A' → Type} (hR : ∀ a a' (x y : R a a'), x = y) :
    {oa : Option A} → {ob : Option A'} → (x y : OptionR A A' R oa ob) → x = y
  | _, _, .none,    .none     => rfl
  | _, _, .some aRel, .some aRel' => by rw [hR _ _ aRel aRel']

/- `OptionR.none`/`OptionR.some` auto-register as the `Option.none`/`Option.some` term primitives (tagging `OptionR`). -/

/- ===================== the graded relator (variance parallel to `paramList`) =====================
   `Option` is a covariant functor (identity variance): the element is needed at exactly the output class. -/

/-- minimal element class per direction for `Option` (pure covariance). -/
def mapOptionVariance : MapClass → ParamClass
  | map0  => (map0,  map0)
  | map1  => (map1,  map0)
  | map2a => (map2a, map0)
  | map2b => (map2b, map0)
  | map3  => (map3,  map0)
  | map4  => (map4,  map0)

/-- element class to build `Option` at output class `c` (identity, via the shared `ParamClass.variance`). -/
def optionVariance (c : ParamClass) : ParamClass := ParamClass.variance mapOptionVariance c

/-- soundness `OptionR` from `Option.map f`, shared by the `2a`/`3`/`4` arms. -/
def optionMapInR {A B : Type} {R : A → B → Type} (f : A → B) (fInR : ∀ a b, f a = b → R a b) :
    ∀ oa ob, Option.map f oa = ob → OptionR A B R oa ob :=
  fun oa ob h => by subst h; cases oa with
    | none => exact .none
    | some a => exact .some (fInR a _ rfl)

/-- completeness `Option.map f` from `OptionR`, shared by the `2b`/`3`/`4` arms. -/
theorem optionRInMap {A B : Type} {R : A → B → Type} (f : A → B) (fRInMap : ∀ a b, R a b → f a = b) :
    ∀ oa ob, OptionR A B R oa ob → Option.map f oa = ob :=
  fun _ _ r => by cases r with
    | none => rfl
    | some aRel => exact congrArg some (fRInMap _ _ aRel)

/-- contra soundness, the mirror of `optionMapInR`. -/
def optionContraMapInR {A B : Type} {R : A → B → Type} (g : B → A) (gInR : ∀ b a, g b = a → R a b) :
    ∀ ob oa, Option.map g ob = oa → OptionR A B R oa ob :=
  fun ob oa h => by subst h; cases ob with
    | none => exact .none
    | some b => exact .some (gInR b _ rfl)

/-- contra completeness, the mirror of `optionRInMap`. -/
theorem optionContraRInMap {A B : Type} {R : A → B → Type} (g : B → A) (gRInMap : ∀ b a, R a b → g b = a) :
    ∀ ob oa, OptionR A B R oa ob → Option.map g ob = oa :=
  fun _ _ r => by cases r with
    | none => rfl
    | some aRel => exact congrArg some (gRInMap _ _ aRel)

/-- the covariant half from the element at `mapOptionVariance m`; the `map4` coherence is free (subsingleton). -/
def optionCov {A B : Type} :
    (m : MapClass) → (pa : Param (mapOptionVariance m).1 (mapOptionVariance m).2 A B) →
    Map m (OptionR A B pa.R)
  | map0,  _  => {}
  | map1,  pa => { map := Option.map pa.cov.map }
  | map2a, pa => { map := Option.map pa.cov.map, mapInR := optionMapInR pa.cov.map pa.cov.mapInR }
  | map2b, pa => { map := Option.map pa.cov.map, rInMap := optionRInMap pa.cov.map pa.cov.rInMap }
  | map3,  pa => { map := Option.map pa.cov.map, mapInR := optionMapInR pa.cov.map pa.cov.mapInR,
                   rInMap := optionRInMap pa.cov.map pa.cov.rInMap }
  | map4,  pa => { map := Option.map pa.cov.map, mapInR := optionMapInR pa.cov.map pa.cov.mapInR,
                   rInMap := optionRInMap pa.cov.map pa.cov.rInMap,
                   rInMapK := fun _ _ _ => OptionR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq) _ _ }

/-- the contravariant half, the mirror of `optionCov`. -/
def optionContra {A B : Type} :
    (n : MapClass) → (pa : Param (mapOptionVariance n).2 (mapOptionVariance n).1 A B) →
    Map n (fun (ob : Option B) (oa : Option A) => OptionR A B pa.R oa ob)
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
