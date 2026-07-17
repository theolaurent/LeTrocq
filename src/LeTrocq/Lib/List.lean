/-
`List` — standard-library registration. `ListR` is the inductive parametricity relation (a TYPE FORMER, so
`⟨·⟩` crosses `List a`; `nil`/`cons` auto-register as term primitives). `paramList` is the graded relator for
`trocq`/`transfer`, element at the `listVariance`-minimal class. User-level: ships here only because `List`
is in the prelude.
-/
import LeTrocq.Driver.Registry
namespace LeTrocq.Lib
open LeTrocq MapClass

/-- two lists related cons-by-cons: same length, corresponding elements `R`-related. The `List` type former. -/
@[trocq] inductive ListR (A A' : Type) (R : A → A' → Type) : List A → List A' → Type
  | nil : ListR A A' R [] []
  | cons {a a' l l'} (aRel : R a a') (lRel : ListR A A' R l l') : ListR A A' R (a :: l) (a' :: l')

/-- the relation is a subsingleton whenever the element relation is — needed for the `(4,4)` coherence. -/
theorem ListR.allEq {A A' : Type} {R : A → A' → Type} (hR : ∀ a a' (x y : R a a'), x = y) :
    {la : List A} → {lb : List A'} → (x y : ListR A A' R la lb) → x = y
  | _, _, .nil,        .nil          => rfl
  | _, _, .cons aRel lRel, .cons aRel' lRel' => by rw [hR _ _ aRel aRel', ListR.allEq hR lRel lRel']

/- `ListR.nil`/`ListR.cons` auto-register as the `List.nil`/`List.cons` term primitives (tagging `ListR`). -/

/- ===================== the graded relator (variance parallel to `paramArrow`) =====================
   `List` is a covariant functor (identity variance): the element is needed at exactly the output class. -/

/-- minimal element class per direction for `List` (pure covariance). -/
def mapListVariance : MapClass → ParamClass
  | map0  => (map0,  map0)
  | map1  => (map1,  map0)
  | map2a => (map2a, map0)
  | map2b => (map2b, map0)
  | map3  => (map3,  map0)
  | map4  => (map4,  map0)

/-- element class to build `List` at output class `c` (identity, via the shared `ParamClass.variance`). -/
def listVariance (c : ParamClass) : ParamClass := ParamClass.variance mapListVariance c

/-- soundness `ListR` from `List.map f`, shared by the `2a`/`3`/`4` arms. (`noncomputable`: `ListR` is data.) -/
noncomputable def listMapInR {A B : Type} {R : A → B → Type} (f : A → B) (fInR : ∀ a b, f a = b → R a b) :
    ∀ la lb, List.map f la = lb → ListR A B R la lb := by
  intro la lb h; subst h
  induction la with
  | nil => exact .nil
  | cons a l ih => exact .cons (fInR a _ rfl) ih

/-- completeness `List.map f` from `ListR`, shared by the `2b`/`3`/`4` arms. -/
theorem listRInMap {A B : Type} {R : A → B → Type} (f : A → B) (fRInMap : ∀ a b, R a b → f a = b) :
    ∀ la lb, ListR A B R la lb → List.map f la = lb := by
  intro _ _ r
  induction r with
  | nil => rfl
  | cons aRel lRel ih => rw [List.map_cons, fRInMap _ _ aRel, ih]

/-- the covariant half from the element at `mapListVariance m`; the `map4` coherence is free (subsingleton). -/
noncomputable def listCov {A B : Type} :
    (m : MapClass) → (pa : Param (mapListVariance m).1 (mapListVariance m).2 A B) →
    Map m (ListR A B pa.R)
  | map0,  _  => {}
  | map1,  pa => { map := List.map pa.cov.map }
  | map2a, pa => { map := List.map pa.cov.map, mapInR := listMapInR pa.cov.map pa.cov.mapInR }
  | map2b, pa => { map := List.map pa.cov.map, rInMap := listRInMap pa.cov.map pa.cov.rInMap }
  | map3,  pa => { map := List.map pa.cov.map, mapInR := listMapInR pa.cov.map pa.cov.mapInR,
                   rInMap := listRInMap pa.cov.map pa.cov.rInMap }
  | map4,  pa => { map := List.map pa.cov.map, mapInR := listMapInR pa.cov.map pa.cov.mapInR,
                   rInMap := listRInMap pa.cov.map pa.cov.rInMap,
                   rInMapK := fun _ _ _ => ListR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq) _ _ }

/-- contra soundness, the mirror of `listMapInR`. -/
noncomputable def listContraMapInR {A B : Type} {R : A → B → Type} (g : B → A) (gInR : ∀ b a, g b = a → R a b) :
    ∀ lb la, List.map g lb = la → ListR A B R la lb := by
  intro lb la h; subst h
  induction lb with
  | nil => exact .nil
  | cons b l ih => exact .cons (gInR b _ rfl) ih

/-- contra completeness, the mirror of `listRInMap`. -/
theorem listContraRInMap {A B : Type} {R : A → B → Type} (g : B → A) (gRInMap : ∀ b a, R a b → g b = a) :
    ∀ lb la, ListR A B R la lb → List.map g lb = la := by
  intro _ _ r
  induction r with
  | nil => rfl
  | cons aRel lRel ih => rw [List.map_cons, gRInMap _ _ aRel, ih]

/-- the contravariant half, the mirror of `listCov`. -/
noncomputable def listContra {A B : Type} :
    (n : MapClass) → (pa : Param (mapListVariance n).2 (mapListVariance n).1 A B) →
    Map n (fun (lb : List B) (la : List A) => ListR A B pa.R la lb)
  | map0,  _  => {}
  | map1,  pa => { map := List.map pa.contra.map }
  | map2a, pa => { map := List.map pa.contra.map, mapInR := listContraMapInR pa.contra.map pa.contra.mapInR }
  | map2b, pa => { map := List.map pa.contra.map, rInMap := listContraRInMap pa.contra.map pa.contra.rInMap }
  | map3,  pa => { map := List.map pa.contra.map, mapInR := listContraMapInR pa.contra.map pa.contra.mapInR,
                   rInMap := listContraRInMap pa.contra.map pa.contra.rInMap }
  | map4,  pa => { map := List.map pa.contra.map, mapInR := listContraMapInR pa.contra.map pa.contra.mapInR,
                   rInMap := listContraRInMap pa.contra.map pa.contra.rInMap,
                   rInMapK := fun _ _ _ => ListR.allEq (fun a a' => (pa.contra.subsingleton a' a).allEq) _ _ }

/-- `List A ≃ List B` at any output class `(m,n)`, element at the `listVariance`-minimal class. Leading `m n`
    so the driver specializes to the demand; weaken obligations by `cases m <;> cases n <;> rfl`. -/
@[trocq] noncomputable def paramList (m n : MapClass) (A B : Type)
    (pa : Param (listVariance (m, n)).1 (listVariance (m, n)).2 A B) :
    Param m n (List A) (List B) where
  R := ListR A B pa.R
  cov := listCov m (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := listContra n (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

end LeTrocq.Lib
