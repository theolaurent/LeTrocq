/-
`Prod` (×, cartesian product) — like `List` but with two type parameters. `ProdR` is the parametricity
relation (a TYPE FORMER over both parameters); its constructor auto-registers as the `Prod.mk` term primitive;
`paramProd` is the graded relator, one `Param` argument per parameter (variance parallel to `List`).
-/
import LeTrocq.Driver.Registry
namespace LeTrocq.Lib
open LeTrocq MapClass

/-- two pairs are related iff their components are componentwise related. -/
@[trocq] inductive ProdR (A A' : Type) (RA : A → A' → Type) (B B' : Type) (RB : B → B' → Type) :
    A × B → A' × B' → Type
  | mk {a a' b b'} (aRel : RA a a') (bRel : RB b b') : ProdR A A' RA B B' RB (a, b) (a', b')

/-- the relation is a subsingleton whenever both component relations are — needed for the `(4,4)` coherence. -/
theorem ProdR.allEq {A A' : Type} {RA : A → A' → Type} {B B' : Type} {RB : B → B' → Type}
    (hA : ∀ a a' (x y : RA a a'), x = y) (hB : ∀ b b' (x y : RB b b'), x = y)
    {p : A × B} {q : A' × B'} (x y : ProdR A A' RA B B' RB p q) : x = y := by
  cases x with | mk aRel bRel => cases y with | mk aRel' bRel' => rw [hA _ _ aRel aRel', hB _ _ bRel bRel']

/- `ProdR.mk` auto-registers as the `Prod.mk` term primitive (tagging `ProdR`). -/

/- ===================== the graded relator (variance parallel to `paramList`) =====================
   `Prod` is a covariant functor in both parameters (identity variance): each component is needed at exactly
   the output class. -/

/-- minimal class per direction of each parameter of `Prod` (pure covariance; same table for both). -/
def mapProdVariance : MapClass → ParamClass
  | map0  => (map0,  map0)
  | map1  => (map1,  map0)
  | map2a => (map2a, map0)
  | map2b => (map2b, map0)
  | map3  => (map3,  map0)
  | map4  => (map4,  map0)

/-- per-parameter class to build `Prod` at output class `c` (identity, via the shared `ParamClass.variance`). -/
def prodVariance (c : ParamClass) : ParamClass := ParamClass.variance mapProdVariance c

/-- soundness `ProdR` from the two component maps, shared by the `2a`/`3`/`4` arms. -/
def prodMapInR {A A' B B' : Type} {RA : A → A' → Type} {RB : B → B' → Type} (f : A → A') (g : B → B')
    (fInR : ∀ a a', f a = a' → RA a a') (gInR : ∀ b b', g b = b' → RB b b') :
    ∀ p q, (f p.1, g p.2) = q → ProdR A A' RA B B' RB p q :=
  fun p _ h => by subst h; exact .mk (fInR p.1 _ rfl) (gInR p.2 _ rfl)

/-- completeness of the two component maps from `ProdR`, shared by the `2b`/`3`/`4` arms. -/
theorem prodRInMap {A A' B B' : Type} {RA : A → A' → Type} {RB : B → B' → Type} (f : A → A') (g : B → B')
    (fRInMap : ∀ a a', RA a a' → f a = a') (gRInMap : ∀ b b', RB b b' → g b = b') :
    ∀ p q, ProdR A A' RA B B' RB p q → (f p.1, g p.2) = q :=
  fun _ _ r => by cases r with | @mk a a' b b' aRel bRel =>
    show (f a, g b) = (a', b'); rw [fRInMap a a' aRel, gRInMap b b' bRel]

/-- contra soundness, the mirror of `prodMapInR`. -/
def prodContraMapInR {A A' B B' : Type} {RA : A → A' → Type} {RB : B → B' → Type} (f : A' → A) (g : B' → B)
    (fInR : ∀ a' a, f a' = a → RA a a') (gInR : ∀ b' b, g b' = b → RB b b') :
    ∀ q p, (f q.1, g q.2) = p → ProdR A A' RA B B' RB p q :=
  fun q _ h => by subst h; exact .mk (fInR q.1 _ rfl) (gInR q.2 _ rfl)

/-- contra completeness, the mirror of `prodRInMap`. -/
theorem prodContraRInMap {A A' B B' : Type} {RA : A → A' → Type} {RB : B → B' → Type} (f : A' → A) (g : B' → B)
    (fRInMap : ∀ a' a, RA a a' → f a' = a) (gRInMap : ∀ b' b, RB b b' → g b' = b) :
    ∀ q p, ProdR A A' RA B B' RB p q → (f q.1, g q.2) = p :=
  fun _ _ r => by cases r with | @mk a a' b b' aRel bRel =>
    show (f a', g b') = (a, b); rw [fRInMap a' a aRel, gRInMap b' b bRel]

/-- the covariant half from the two components at `mapProdVariance m`; the `map4` coherence is free (subsingleton). -/
def prodCov {A A' B B' : Type} :
    (m : MapClass) →
    (pa : Param (mapProdVariance m).1 (mapProdVariance m).2 A A') →
    (pb : Param (mapProdVariance m).1 (mapProdVariance m).2 B B') →
    MapHas m (ProdR A A' pa.R B B' pb.R)
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := fun p => (pa.cov.map p.1, pb.cov.map p.2) }
  | map2a, pa, pb => { map := fun p => (pa.cov.map p.1, pb.cov.map p.2),
                       mapInR := prodMapInR pa.cov.map pb.cov.map pa.cov.mapInR pb.cov.mapInR }
  | map2b, pa, pb => { map := fun p => (pa.cov.map p.1, pb.cov.map p.2),
                       rInMap := prodRInMap pa.cov.map pb.cov.map pa.cov.rInMap pb.cov.rInMap }
  | map3,  pa, pb => { map := fun p => (pa.cov.map p.1, pb.cov.map p.2),
                       mapInR := prodMapInR pa.cov.map pb.cov.map pa.cov.mapInR pb.cov.mapInR,
                       rInMap := prodRInMap pa.cov.map pb.cov.map pa.cov.rInMap pb.cov.rInMap }
  | map4,  pa, pb => { map := fun p => (pa.cov.map p.1, pb.cov.map p.2),
                       mapInR := prodMapInR pa.cov.map pb.cov.map pa.cov.mapInR pb.cov.mapInR,
                       rInMap := prodRInMap pa.cov.map pb.cov.map pa.cov.rInMap pb.cov.rInMap,
                       rInMapK := fun _ _ _ => ProdR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq)
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
                       mapInR := prodContraMapInR pa.contra.map pb.contra.map pa.contra.mapInR pb.contra.mapInR }
  | map2b, pa, pb => { map := fun q => (pa.contra.map q.1, pb.contra.map q.2),
                       rInMap := prodContraRInMap pa.contra.map pb.contra.map pa.contra.rInMap pb.contra.rInMap }
  | map3,  pa, pb => { map := fun q => (pa.contra.map q.1, pb.contra.map q.2),
                       mapInR := prodContraMapInR pa.contra.map pb.contra.map pa.contra.mapInR pb.contra.mapInR,
                       rInMap := prodContraRInMap pa.contra.map pb.contra.map pa.contra.rInMap pb.contra.rInMap }
  | map4,  pa, pb => { map := fun q => (pa.contra.map q.1, pb.contra.map q.2),
                       mapInR := prodContraMapInR pa.contra.map pb.contra.map pa.contra.mapInR pb.contra.mapInR,
                       rInMap := prodContraRInMap pa.contra.map pb.contra.map pa.contra.rInMap pb.contra.rInMap,
                       rInMapK := fun _ _ _ => ProdR.allEq (fun a a' => (pa.contra.subsingleton a' a).allEq)
                         (fun b b' => (pb.contra.subsingleton b' b).allEq) _ _ }

/-- `A × B ≃ A' × B'` at ANY output class `(m,n)`, each component at the `prodVariance`-minimal class. -/
@[trocq] noncomputable def paramProd (m n : MapClass) (A A' : Type)
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
