/-
The LeTrocq STANDARD LIBRARY: `List`.

`List : Type → Type` is a *relator*: its witness lifts an element relation to a relation on lists, itself an
INDUCTIVE (`ListR`, one constructor per `List`'s). It registers base-agnostically on BOTH surfaces:

  • the TERM surface (`⟨·⟩`/`[·]`): `ListR` is the parametricity RELATION, registered as a TYPE FORMER so `⟨·⟩`
    crosses `List a` (counterpart head `List ↦ List`); `List.nil`/`List.cons` are TERM primitives with
    relatedness `ListR.nil`/`ListR.cons`.
  • the tactic path (`trocq`/`transfer%`): the GRADED relator `paramListRG`, building `List` at ANY output class
    with the element at the `listVariance`-minimal class (parallel to `paramArrow`); completeness laws are
    inductions, and `R_in_mapK` is free once the element relation is a subsingleton.

A USER-LEVEL registration (it sits in the library only because `List` is in the prelude).
-/
import LeTrocq.Driver.Registry
namespace LeTrocq.Lib
open LeTrocq MapClass

/-- two lists are related iff they are cons-by-cons related: same length, corresponding elements `R`-related.
    This is the canonical relational interpretation of the inductive `List`. Its first three parameters
    `(A, A', R)` are the element's `(A, A', RA)` triple that the graded relator `paramListRG` threads in; the
    two list INDICES are read off as the related objects, so `@[trocq]` classifies it as the `List` type former. -/
@[trocq] inductive ListR (A A' : Type) (R : A → A' → Type) : List A → List A' → Type
  | nil : ListR A A' R [] []
  | cons {a a' l l'} (aR : R a a') (lR : ListR A A' R l l') : ListR A A' R (a :: l) (a' :: l')

/-- the relation is a subsingleton whenever the element relation is — needed for the `(4,4)` coherence. -/
theorem ListR.allEq {A A' : Type} {R : A → A' → Type} (hR : ∀ a a' (x y : R a a'), x = y) :
    {la : List A} → {lb : List A'} → (x y : ListR A A' R la lb) → x = y
  | _, _, .nil,        .nil          => rfl
  | _, _, .cons aR lR, .cons aR' lR' => by rw [hR _ _ aR aR', ListR.allEq hR lR lR']

/- ===================== the constructors as TERM primitives (for `translate%` / `relate%`) =====================
   In abstraction-theorem triple form `(A,A',R) (a,a',aR) (l,l',lR)`, returning the inductive's constructors;
   the head `List.nil`/`List.cons` on each side is read off the conclusion, so these are term primitives. -/
@[trocq] def ListNilR (A A' : Type) (R : A → A' → Type) : ListR A A' R [] [] := .nil
@[trocq] def ListConsR (A A' : Type) (R : A → A' → Type)
    (a : A) (a' : A') (aR : R a a') (l : List A) (l' : List A') (lR : ListR A A' R l l') :
    ListR A A' R (a :: l) (a' :: l') := .cons aR lR

/- ===================== the GRADED relator (variance mechanism, parallel to `paramArrow`) =====================
   `List` is a COVARIANT functor, so its variance is the identity: to build `List` at output class `(m,n)` the
   element is needed at exactly `(m,n)`. `mapListVariance` is the per-direction primitive table (like
   `mapArrowVariance`), `listVariance` the demand→element-class map the driver inverts, and `paramListRG` the
   class-indexed family (like `paramArrow`) — each `cov`/`contra` arm using only the fields available at its
   class. This lets the driver build `List X` at the DEMANDED class, so an element that cannot reach `(4,4)`
   (a universe, a polymorphic type) still transfers at a lower demand. -/

/-- per-map-class minimal element class for `List` (pure covariance: the element is needed at exactly the
    list's class in that direction). Parallel to `mapArrowVariance`. -/
def mapListVariance : MapClass → ParamClass
  | map0  => (map0,  map0)
  | map1  => (map1,  map0)
  | map2a => (map2a, map0)
  | map2b => (map2b, map0)
  | map3  => (map3,  map0)
  | map4  => (map4,  map0)

/-- minimal element class to build `List` at output class `c`: the cov requirement joined with the negated
    contra one. Identity (`List` is covariant), but computed through the same combinator as `arrowVariance`. -/
def listVariance (c : ParamClass) : ParamClass :=
  ParamClass.join (mapListVariance c.1) (ParamClass.negate (mapListVariance c.2))

/-- the lifted soundness proof: `ListR` from `List.map f`, written ONCE for the `map2a`/`map3`/`map4` arms.
    (`noncomputable def`, not `theorem`: `ListR` is `Type`-valued data built via `List.rec`.) -/
noncomputable def listMapInR {A B : Type} {R : A → B → Type} (f : A → B) (fInR : ∀ a b, f a = b → R a b) :
    ∀ la lb, List.map f la = lb → ListR A B R la lb := by
  intro la lb h; subst h
  induction la with
  | nil => exact .nil
  | cons a l ih => exact .cons (fInR a _ rfl) ih

/-- the lifted completeness proof: `List.map f` from `ListR`, written ONCE for the `map2b`/`map3`/`map4` arms. -/
theorem listRInMap {A B : Type} {R : A → B → Type} (f : A → B) (fRInMap : ∀ a b, R a b → f a = b) :
    ∀ la lb, ListR A B R la lb → List.map f la = lb := by
  intro _ _ r
  induction r with
  | nil => rfl
  | cons aR lR ih => rw [List.map_cons, fRInMap _ _ aR, ih]

/-- the covariant half `MapHas m (ListR R)` from the element at `mapListVariance m`. At `map4` the coherence
    is free: a class-4 element relation is a subsingleton, so `ListR.allEq` applies. -/
noncomputable def listCov {A B : Type} :
    (m : MapClass) → (pa : Param (mapListVariance m).1 (mapListVariance m).2 A B) →
    MapHas m (ListR A B pa.R)
  | map0,  _  => {}
  | map1,  pa => { map := List.map pa.cov.map }
  | map2a, pa => { map := List.map pa.cov.map, map_in_R := listMapInR pa.cov.map pa.cov.map_in_R }
  | map2b, pa => { map := List.map pa.cov.map, R_in_map := listRInMap pa.cov.map pa.cov.R_in_map }
  | map3,  pa => { map := List.map pa.cov.map, map_in_R := listMapInR pa.cov.map pa.cov.map_in_R,
                   R_in_map := listRInMap pa.cov.map pa.cov.R_in_map }
  | map4,  pa => { map := List.map pa.cov.map, map_in_R := listMapInR pa.cov.map pa.cov.map_in_R,
                   R_in_map := listRInMap pa.cov.map pa.cov.R_in_map,
                   R_in_mapK := fun _ _ _ => ListR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq) _ _ }

/-- contra soundness: `ListR` from `List.map g` on the B-side list — the mirror of `listMapInR`. -/
noncomputable def listContraMapInR {A B : Type} {R : A → B → Type} (g : B → A) (gInR : ∀ b a, g b = a → R a b) :
    ∀ lb la, List.map g lb = la → ListR A B R la lb := by
  intro lb la h; subst h
  induction lb with
  | nil => exact .nil
  | cons b l ih => exact .cons (gInR b _ rfl) ih

/-- contra completeness: `List.map g` on the B-side list from `ListR` — the mirror of `listRInMap`. -/
theorem listContraRInMap {A B : Type} {R : A → B → Type} (g : B → A) (gRInMap : ∀ b a, R a b → g b = a) :
    ∀ lb la, ListR A B R la lb → List.map g lb = la := by
  intro _ _ r
  induction r with
  | nil => rfl
  | cons aR lR ih => rw [List.map_cons, gRInMap _ _ aR, ih]

/-- the contravariant half `MapHas n (flip (ListR R))` from the element's contra at `mapListVariance n`. -/
noncomputable def listContra {A B : Type} :
    (n : MapClass) → (pa : Param (mapListVariance n).2 (mapListVariance n).1 A B) →
    MapHas n (fun (lb : List B) (la : List A) => ListR A B pa.R la lb)
  | map0,  _  => {}
  | map1,  pa => { map := List.map pa.contra.map }
  | map2a, pa => { map := List.map pa.contra.map, map_in_R := listContraMapInR pa.contra.map pa.contra.map_in_R }
  | map2b, pa => { map := List.map pa.contra.map, R_in_map := listContraRInMap pa.contra.map pa.contra.R_in_map }
  | map3,  pa => { map := List.map pa.contra.map, map_in_R := listContraMapInR pa.contra.map pa.contra.map_in_R,
                   R_in_map := listContraRInMap pa.contra.map pa.contra.R_in_map }
  | map4,  pa => { map := List.map pa.contra.map, map_in_R := listContraMapInR pa.contra.map pa.contra.map_in_R,
                   R_in_map := listContraRInMap pa.contra.map pa.contra.R_in_map,
                   R_in_mapK := fun _ _ _ => ListR.allEq (fun a a' => (pa.contra.subsingleton a' a).allEq) _ _ }

/-- `List A ≃ List B` at ANY output class `(m,n)`, from the element at the `listVariance`-minimal class. The
    single element witness is weakened to what each half consumes; every obligation is `join ≥ component`,
    discharged by `cases m <;> cases n <;> rfl`. The output classes `m n` are the LEADING arguments so the
    driver can specialize `paramListRG m n` to the demand and read the element class off the residual type. -/
@[trocq] noncomputable def paramListRG (m n : MapClass) (A B : Type)
    (pa : Param (listVariance (m, n)).1 (listVariance (m, n)).2 A B) :
    Param m n (List A) (List B) where
  R := ListR A B pa.R
  cov := listCov m (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := listContra n (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

end LeTrocq.Lib
