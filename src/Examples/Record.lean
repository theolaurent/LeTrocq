/-
User-written example: a record `Pt` whose parametricity relation `PtR` is authored as a `structure` (fields
relating the projections). Tagging it auto-registers each field `PtR.xR`/`PtR.yR` as the term primitive for
the projection `Pt.x`/`Pt.y`, and the constructor `Pt.mk`, so `translate`/`relate` cross them with no proxy.
The graded relator `paramPt` is hand-written like every type former; `Pt` is a covariant functor in its one
parameter, so its variance is the identity (parallel to `paramList`). (A `class`-authored variant: Group.lean.)
-/
import LeTrocq
namespace LeTrocq.Examples
open LeTrocq MapClass

/- ===================== a record and its relation, authored as a STRUCTURE ===================== -/
structure Pt (T : Type) where
  x : T
  y : T
deriving Repr

/-- two points are related iff their fields are `RA`-related. Tagging this structure auto-registers
    `Pt.x`/`Pt.y` and `Pt.mk` as term primitives. -/
@[trocq] structure PtR (A A' : Type) (RA : A → A' → Type) (p : Pt A) (p' : Pt A') where
  xR : RA p.x p'.x
  yR : RA p.y p'.y

/-- the relation is a subsingleton when the field relation is — needed for the `(4,4)` coherence. -/
theorem PtR.allEq {A A' : Type} {RA : A → A' → Type} (hR : ∀ a a' (x y : RA a a'), x = y)
    {p : Pt A} {q : Pt A'} (u v : PtR A A' RA p q) : u = v := by
  cases u with | mk ux uy => cases v with | mk vx vy => rw [hR _ _ ux vx, hR _ _ uy vy]

/- ===================== the GRADED relator (variance mechanism, covariant — parallel to `List`) ===================== -/
/-- the shared forward map: apply the element map to both fields. -/
def ptMap {A B : Type} (f : A → B) (p : Pt A) : Pt B := ⟨f p.x, f p.y⟩

/-- lifted soundness `PtR` from `ptMap f`, shared across the `map2a`/`map3`/`map4` arms (cov + contra mirror). -/
def ptMapInR {A B : Type} {R : A → B → Type} (f : A → B) (fInR : ∀ a b, f a = b → R a b) :
    ∀ p q, ptMap f p = q → PtR A B R p q := by
  intro p q h; subst h; exact ⟨fInR _ _ rfl, fInR _ _ rfl⟩

/-- lifted completeness `ptMap f` from `PtR`, shared across the `map2b`/`map3`/`map4` arms. -/
theorem ptRInMap {A B : Type} {R : A → B → Type} (f : A → B) (fRInMap : ∀ a b, R a b → f a = b) :
    ∀ p q, PtR A B R p q → ptMap f p = q := by
  intro p q r; obtain ⟨qx, qy⟩ := q
  show (⟨f p.x, f p.y⟩ : Pt B) = ⟨qx, qy⟩
  rw [fRInMap _ _ r.xR, fRInMap _ _ r.yR]

/-- contra soundness: `PtR` from `ptMap g` on the B-side point — the mirror of `ptMapInR`. -/
def ptContraMapInR {A B : Type} {R : A → B → Type} (g : B → A) (gInR : ∀ b a, g b = a → R a b) :
    ∀ q p, ptMap g q = p → PtR A B R p q := by
  intro q p h; subst h; exact ⟨gInR _ _ rfl, gInR _ _ rfl⟩

/-- contra completeness: `ptMap g` on the B-side point from `PtR` — the mirror of `ptRInMap`. -/
theorem ptContraRInMap {A B : Type} {R : A → B → Type} (g : B → A) (gRInMap : ∀ b a, R a b → g b = a) :
    ∀ q p, PtR A B R p q → ptMap g q = p := by
  intro q p r; obtain ⟨px, py⟩ := p
  show (⟨g q.x, g q.y⟩ : Pt A) = ⟨px, py⟩
  rw [gRInMap _ _ r.xR, gRInMap _ _ r.yR]

/-- per-map-class minimal element class for `Pt` (pure covariance; identity — parallel to `mapListVariance`). -/
def mapPtVariance : MapClass → ParamClass
  | map0  => (map0,  map0)
  | map1  => (map1,  map0)
  | map2a => (map2a, map0)
  | map2b => (map2b, map0)
  | map3  => (map3,  map0)
  | map4  => (map4,  map0)

/-- minimal element class to build `Pt` at output class `c` (identity — covariant). -/
def ptVariance (c : ParamClass) : ParamClass :=
  ParamClass.join (mapPtVariance c.1) (ParamClass.negate (mapPtVariance c.2))

/-- the covariant half `Map m (PtR R)` from the element at `mapPtVariance m`. -/
def ptCov {A B : Type} :
    (m : MapClass) → (pa : Param (mapPtVariance m).1 (mapPtVariance m).2 A B) →
    Map m (PtR A B pa.R)
  | map0,  _  => {}
  | map1,  pa => { map := ptMap pa.cov.map }
  | map2a, pa => { map := ptMap pa.cov.map, mapInR := ptMapInR pa.cov.map pa.cov.mapInR }
  | map2b, pa => { map := ptMap pa.cov.map, rInMap := ptRInMap pa.cov.map pa.cov.rInMap }
  | map3,  pa => { map := ptMap pa.cov.map, mapInR := ptMapInR pa.cov.map pa.cov.mapInR,
                   rInMap := ptRInMap pa.cov.map pa.cov.rInMap }
  | map4,  pa => { map := ptMap pa.cov.map, mapInR := ptMapInR pa.cov.map pa.cov.mapInR,
                   rInMap := ptRInMap pa.cov.map pa.cov.rInMap,
                   rInMapK := fun _ _ _ => PtR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq) _ _ }

/-- the contravariant half `Map n (flip (PtR R))` from the element's contra at `mapPtVariance n`. -/
def ptContra {A B : Type} :
    (n : MapClass) → (pa : Param (mapPtVariance n).2 (mapPtVariance n).1 A B) →
    Map n (fun (q : Pt B) (p : Pt A) => PtR A B pa.R p q)
  | map0,  _  => {}
  | map1,  pa => { map := ptMap pa.contra.map }
  | map2a, pa => { map := ptMap pa.contra.map, mapInR := ptContraMapInR pa.contra.map pa.contra.mapInR }
  | map2b, pa => { map := ptMap pa.contra.map, rInMap := ptContraRInMap pa.contra.map pa.contra.rInMap }
  | map3,  pa => { map := ptMap pa.contra.map, mapInR := ptContraMapInR pa.contra.map pa.contra.mapInR,
                   rInMap := ptContraRInMap pa.contra.map pa.contra.rInMap }
  | map4,  pa => { map := ptMap pa.contra.map, mapInR := ptContraMapInR pa.contra.map pa.contra.mapInR,
                   rInMap := ptContraRInMap pa.contra.map pa.contra.rInMap,
                   rInMapK := fun _ _ _ => PtR.allEq (fun a a' => (pa.contra.subsingleton a' a).allEq) _ _ }

/-- `Pt A ≃ Pt B` at ANY output class `(m,n)`, element at the `ptVariance`-minimal class. -/
@[trocq] def paramPt (m n : MapClass) (A B : Type)
    (pa : Param (ptVariance (m, n)).1 (ptVariance (m, n)).2 A B) :
    Param m n (Pt A) (Pt B) where
  R := PtR A B pa.R
  cov := ptCov m (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := ptContra n (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

end LeTrocq.Examples
