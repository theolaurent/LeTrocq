/-
The LeTrocq STANDARD LIBRARY: `Prod` (×, the cartesian product).

`List` with TWO type parameters instead of one — and non-dependent (unlike `Sigma`, whose second component
lives over the first). `ProdR` is the parametricity relation (a TYPE FORMER over both parameters: the
translation crosses `A × B` by feeding each parameter's `(_, _, _)` triple in turn), `ProdMkR` the
constructor TERM primitive, `paramProdRG` the GRADED relator (variance parallel to `List`, one `Param` argument
per parameter).
-/
import LeTrocq.Driver.Registry
namespace LeTrocq.Lib
open LeTrocq MapClass

/-- two pairs are related iff their components are componentwise related. The parameter order
    `(A, A', RA, B, B', RB)` is what the translation supplies (one `mkApp3` triple per type parameter). -/
@[trocq] inductive ProdR (A A' : Type) (RA : A → A' → Type) (B B' : Type) (RB : B → B' → Type) :
    A × B → A' × B' → Type
  | mk {a a' b b'} (aR : RA a a') (bR : RB b b') : ProdR A A' RA B B' RB (a, b) (a', b')

theorem ProdR.allEq {A A' : Type} {RA : A → A' → Type} {B B' : Type} {RB : B → B' → Type}
    (hA : ∀ a a' (x y : RA a a'), x = y) (hB : ∀ b b' (x y : RB b b'), x = y)
    {p : A × B} {q : A' × B'} (x y : ProdR A A' RA B B' RB p q) : x = y := by
  cases x with | mk aR bR => cases y with | mk aR' bR' => rw [hA _ _ aR aR', hB _ _ bR bR']

/-- `Prod.mk` as a TERM primitive: the four triples are the two type parameters then the two components. -/
@[trocq] def ProdMkR (A A' : Type) (RA : A → A' → Type) (B B' : Type) (RB : B → B' → Type)
    (a : A) (a' : A') (aR : RA a a') (b : B) (b' : B') (bR : RB b b') :
    ProdR A A' RA B B' RB (a, b) (a', b') := .mk aR bR

/- ===================== the GRADED relator (variance mechanism, parallel to `List`) =====================
   `Prod` is covariant in BOTH parameters, each with the identity variance of a covariant functor: at output
   class `(m,n)` each component is needed at exactly `(m,n)`. `mapProdVariance` is the shared per-parameter
   table (both parameters use it), and `paramProdRG` builds the pair at any output class. -/

/-- per-map-class minimal class of EACH parameter of `Prod` (pure covariance; the same table for both). -/
def mapProdVariance : MapClass → ParamClass
  | map0  => (map0,  map0)
  | map1  => (map1,  map0)
  | map2a => (map2a, map0)
  | map2b => (map2b, map0)
  | map3  => (map3,  map0)
  | map4  => (map4,  map0)

/-- minimal per-parameter class to build `Prod` at output class `c` (identity — both parameters covariant). -/
def prodVariance (c : ParamClass) : ParamClass :=
  ParamClass.join (mapProdVariance c.1) (ParamClass.negate (mapProdVariance c.2))

/-- lifted soundness/completeness for `ProdR` over both components, shared across the `prodCov`/`prodContra`
    arms (the contra arms swap each component's map direction). No recursion, so computable. -/
def prodMapInR {A A' B B' : Type} {RA : A → A' → Type} {RB : B → B' → Type} (f : A → A') (g : B → B')
    (fInR : ∀ a a', f a = a' → RA a a') (gInR : ∀ b b', g b = b' → RB b b') :
    ∀ p q, (f p.1, g p.2) = q → ProdR A A' RA B B' RB p q :=
  fun p _ h => by subst h; exact .mk (fInR p.1 _ rfl) (gInR p.2 _ rfl)

theorem prodRInMap {A A' B B' : Type} {RA : A → A' → Type} {RB : B → B' → Type} (f : A → A') (g : B → B')
    (fRInMap : ∀ a a', RA a a' → f a = a') (gRInMap : ∀ b b', RB b b' → g b = b') :
    ∀ p q, ProdR A A' RA B B' RB p q → (f p.1, g p.2) = q :=
  fun _ _ r => by cases r with | @mk a a' b b' aR bR =>
    show (f a, g b) = (a', b'); rw [fRInMap a a' aR, gRInMap b b' bR]

def prodContraMapInR {A A' B B' : Type} {RA : A → A' → Type} {RB : B → B' → Type} (f : A' → A) (g : B' → B)
    (fInR : ∀ a' a, f a' = a → RA a a') (gInR : ∀ b' b, g b' = b → RB b b') :
    ∀ q p, (f q.1, g q.2) = p → ProdR A A' RA B B' RB p q :=
  fun q _ h => by subst h; exact .mk (fInR q.1 _ rfl) (gInR q.2 _ rfl)

theorem prodContraRInMap {A A' B B' : Type} {RA : A → A' → Type} {RB : B → B' → Type} (f : A' → A) (g : B' → B)
    (fRInMap : ∀ a' a, RA a a' → f a' = a) (gRInMap : ∀ b' b, RB b b' → g b' = b) :
    ∀ q p, ProdR A A' RA B B' RB p q → (f q.1, g q.2) = p :=
  fun _ _ r => by cases r with | @mk a a' b b' aR bR =>
    show (f a', g b') = (a, b); rw [fRInMap a' a aR, gRInMap b' b bR]

/-- the covariant half from the two components at `mapProdVariance m`. -/
def prodCov {A A' B B' : Type} :
    (m : MapClass) →
    (pa : Param (mapProdVariance m).1 (mapProdVariance m).2 A A') →
    (pb : Param (mapProdVariance m).1 (mapProdVariance m).2 B B') →
    MapHas m (ProdR A A' pa.R B B' pb.R)
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := fun p => (pa.cov.map p.1, pb.cov.map p.2) }
  | map2a, pa, pb => { map := fun p => (pa.cov.map p.1, pb.cov.map p.2),
                       map_in_R := prodMapInR pa.cov.map pb.cov.map pa.cov.map_in_R pb.cov.map_in_R }
  | map2b, pa, pb => { map := fun p => (pa.cov.map p.1, pb.cov.map p.2),
                       R_in_map := prodRInMap pa.cov.map pb.cov.map pa.cov.R_in_map pb.cov.R_in_map }
  | map3,  pa, pb => { map := fun p => (pa.cov.map p.1, pb.cov.map p.2),
                       map_in_R := prodMapInR pa.cov.map pb.cov.map pa.cov.map_in_R pb.cov.map_in_R,
                       R_in_map := prodRInMap pa.cov.map pb.cov.map pa.cov.R_in_map pb.cov.R_in_map }
  | map4,  pa, pb => { map := fun p => (pa.cov.map p.1, pb.cov.map p.2),
                       map_in_R := prodMapInR pa.cov.map pb.cov.map pa.cov.map_in_R pb.cov.map_in_R,
                       R_in_map := prodRInMap pa.cov.map pb.cov.map pa.cov.R_in_map pb.cov.R_in_map,
                       R_in_mapK := fun _ _ _ => ProdR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq)
                         (fun b b' => (pb.cov.subsingleton b b').allEq) _ _ }

/-- the contravariant half from the two components' contra at `mapProdVariance n`. -/
def prodContra {A A' B B' : Type} :
    (n : MapClass) →
    (pa : Param (mapProdVariance n).2 (mapProdVariance n).1 A A') →
    (pb : Param (mapProdVariance n).2 (mapProdVariance n).1 B B') →
    MapHas n (fun (q : A' × B') (p : A × B) => ProdR A A' pa.R B B' pb.R p q)
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := fun q => (pa.contra.map q.1, pb.contra.map q.2) }
  | map2a, pa, pb => { map := fun q => (pa.contra.map q.1, pb.contra.map q.2),
                       map_in_R := prodContraMapInR pa.contra.map pb.contra.map pa.contra.map_in_R pb.contra.map_in_R }
  | map2b, pa, pb => { map := fun q => (pa.contra.map q.1, pb.contra.map q.2),
                       R_in_map := prodContraRInMap pa.contra.map pb.contra.map pa.contra.R_in_map pb.contra.R_in_map }
  | map3,  pa, pb => { map := fun q => (pa.contra.map q.1, pb.contra.map q.2),
                       map_in_R := prodContraMapInR pa.contra.map pb.contra.map pa.contra.map_in_R pb.contra.map_in_R,
                       R_in_map := prodContraRInMap pa.contra.map pb.contra.map pa.contra.R_in_map pb.contra.R_in_map }
  | map4,  pa, pb => { map := fun q => (pa.contra.map q.1, pb.contra.map q.2),
                       map_in_R := prodContraMapInR pa.contra.map pb.contra.map pa.contra.map_in_R pb.contra.map_in_R,
                       R_in_map := prodContraRInMap pa.contra.map pb.contra.map pa.contra.R_in_map pb.contra.R_in_map,
                       R_in_mapK := fun _ _ _ => ProdR.allEq (fun a a' => (pa.contra.subsingleton a' a).allEq)
                         (fun b b' => (pb.contra.subsingleton b' b).allEq) _ _ }

/-- `A × B ≃ A' × B'` at ANY output class `(m,n)`, each component at the `prodVariance`-minimal class. -/
@[trocq] noncomputable def paramProdRG (m n : MapClass) (A A' : Type)
    (pa : Param (prodVariance (m, n)).1 (prodVariance (m, n)).2 A A')
    (B B' : Type)
    (pb : Param (prodVariance (m, n)).1 (prodVariance (m, n)).2 B B') :
    Param m n (A × B) (A' × B') where
  R := ProdR A A' pa.R B B' pb.R
  cov := prodCov m (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (pb.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := prodContra n (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (pb.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

end LeTrocq.Lib
