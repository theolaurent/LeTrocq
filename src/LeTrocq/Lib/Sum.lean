/-
The LeTrocq STANDARD LIBRARY: `Sum` (⊕, the non-dependent disjoint union).

Two type parameters (like `Prod`) but two constructors (like `Option`): `SumR` is the parametricity relation
(`inl ~ inl`, `inr ~ inr`), `SumInlR`/`SumInrR` the constructor TERM primitives, `paramSum` the GRADED
relator (variance parallel to `List`). The forward map is `Sum.map` of the two component maps.
-/
import LeTrocq.Driver.Registry
namespace LeTrocq.Lib
open LeTrocq MapClass

/-- two sums are related iff they take the same injection with componentwise-related payloads. -/
@[trocq] inductive SumR (A A' : Type) (RA : A → A' → Type) (B B' : Type) (RB : B → B' → Type) :
    A ⊕ B → A' ⊕ B' → Type
  | inl {a a'} (aRel : RA a a') : SumR A A' RA B B' RB (.inl a) (.inl a')
  | inr {b b'} (bRel : RB b b') : SumR A A' RA B B' RB (.inr b) (.inr b')

theorem SumR.allEq {A A' : Type} {RA : A → A' → Type} {B B' : Type} {RB : B → B' → Type}
    (hA : ∀ a a' (x y : RA a a'), x = y) (hB : ∀ b b' (x y : RB b b'), x = y) :
    {s : A ⊕ B} → {t : A' ⊕ B'} → (x y : SumR A A' RA B B' RB s t) → x = y
  | _, _, .inl aRel, .inl aRel' => by rw [hA _ _ aRel aRel']
  | _, _, .inr bRel, .inr bRel' => by rw [hB _ _ bRel bRel']

/-- the two constructors as TERM primitives (the OTHER summand's type still crosses, as the unused triple). -/
@[trocq] def SumInlR (A A' : Type) (RA : A → A' → Type) (B B' : Type) (RB : B → B' → Type)
    (a : A) (a' : A') (aRel : RA a a') : SumR A A' RA B B' RB (.inl a) (.inl a') := .inl aRel
@[trocq] def SumInrR (A A' : Type) (RA : A → A' → Type) (B B' : Type) (RB : B → B' → Type)
    (b : B) (b' : B') (bRel : RB b b') : SumR A A' RA B B' RB (.inr b) (.inr b') := .inr bRel

/- ===================== the GRADED relator (variance mechanism, parallel to `List`) =====================
   `Sum` is covariant in both summands, identity variance (a covariant functor): at output class `(m,n)` each
   summand is needed at exactly `(m,n)`. Same shape as `paramProd`, with the two injections in place of the
   pair projections. -/

/-- per-map-class minimal class of EACH summand of `Sum` (pure covariance; the same table for both). -/
def mapSumVariance : MapClass → ParamClass
  | map0  => (map0,  map0)
  | map1  => (map1,  map0)
  | map2a => (map2a, map0)
  | map2b => (map2b, map0)
  | map3  => (map3,  map0)
  | map4  => (map4,  map0)

/-- minimal per-summand class to build `Sum` at output class `c` (identity — both summands covariant). -/
def sumVariance (c : ParamClass) : ParamClass :=
  ParamClass.join (mapSumVariance c.1) (ParamClass.negate (mapSumVariance c.2))

/-- lifted soundness/completeness for `SumR` over both summands, shared across the `sumCov`/`sumContra`
    arms (contra swaps each summand's map direction). No recursion, so computable. -/
def sumMapInR {A A' B B' : Type} {RA : A → A' → Type} {RB : B → B' → Type} (f : A → A') (g : B → B')
    (fInR : ∀ a a', f a = a' → RA a a') (gInR : ∀ b b', g b = b' → RB b b') :
    ∀ s t, Sum.map f g s = t → SumR A A' RA B B' RB s t :=
  fun s _ h => by subst h; cases s with
    | inl a => exact .inl (fInR a _ rfl)
    | inr b => exact .inr (gInR b _ rfl)

theorem sumRInMap {A A' B B' : Type} {RA : A → A' → Type} {RB : B → B' → Type} (f : A → A') (g : B → B')
    (fRInMap : ∀ a a', RA a a' → f a = a') (gRInMap : ∀ b b', RB b b' → g b = b') :
    ∀ s t, SumR A A' RA B B' RB s t → Sum.map f g s = t :=
  fun _ _ r => by cases r with
    | inl aRel => exact congrArg Sum.inl (fRInMap _ _ aRel)
    | inr bRel => exact congrArg Sum.inr (gRInMap _ _ bRel)

def sumContraMapInR {A A' B B' : Type} {RA : A → A' → Type} {RB : B → B' → Type} (f : A' → A) (g : B' → B)
    (fInR : ∀ a' a, f a' = a → RA a a') (gInR : ∀ b' b, g b' = b → RB b b') :
    ∀ t s, Sum.map f g t = s → SumR A A' RA B B' RB s t :=
  fun t _ h => by subst h; cases t with
    | inl a => exact .inl (fInR a _ rfl)
    | inr b => exact .inr (gInR b _ rfl)

theorem sumContraRInMap {A A' B B' : Type} {RA : A → A' → Type} {RB : B → B' → Type} (f : A' → A) (g : B' → B)
    (fRInMap : ∀ a' a, RA a a' → f a' = a) (gRInMap : ∀ b' b, RB b b' → g b' = b) :
    ∀ t s, SumR A A' RA B B' RB s t → Sum.map f g t = s :=
  fun _ _ r => by cases r with
    | inl aRel => exact congrArg Sum.inl (fRInMap _ _ aRel)
    | inr bRel => exact congrArg Sum.inr (gRInMap _ _ bRel)

/-- the covariant half from the two summands at `mapSumVariance m`. -/
def sumCov {A A' B B' : Type} :
    (m : MapClass) →
    (pa : Param (mapSumVariance m).1 (mapSumVariance m).2 A A') →
    (pb : Param (mapSumVariance m).1 (mapSumVariance m).2 B B') →
    MapHas m (SumR A A' pa.R B B' pb.R)
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := Sum.map pa.cov.map pb.cov.map }
  | map2a, pa, pb => { map := Sum.map pa.cov.map pb.cov.map,
                       mapInR := sumMapInR pa.cov.map pb.cov.map pa.cov.mapInR pb.cov.mapInR }
  | map2b, pa, pb => { map := Sum.map pa.cov.map pb.cov.map,
                       rInMap := sumRInMap pa.cov.map pb.cov.map pa.cov.rInMap pb.cov.rInMap }
  | map3,  pa, pb => { map := Sum.map pa.cov.map pb.cov.map,
                       mapInR := sumMapInR pa.cov.map pb.cov.map pa.cov.mapInR pb.cov.mapInR,
                       rInMap := sumRInMap pa.cov.map pb.cov.map pa.cov.rInMap pb.cov.rInMap }
  | map4,  pa, pb => { map := Sum.map pa.cov.map pb.cov.map,
                       mapInR := sumMapInR pa.cov.map pb.cov.map pa.cov.mapInR pb.cov.mapInR,
                       rInMap := sumRInMap pa.cov.map pb.cov.map pa.cov.rInMap pb.cov.rInMap,
                       rInMapK := fun _ _ _ => SumR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq)
                         (fun b b' => (pb.cov.subsingleton b b').allEq) _ _ }

/-- the contravariant half from the two summands' contra at `mapSumVariance n`. -/
def sumContra {A A' B B' : Type} :
    (n : MapClass) →
    (pa : Param (mapSumVariance n).2 (mapSumVariance n).1 A A') →
    (pb : Param (mapSumVariance n).2 (mapSumVariance n).1 B B') →
    MapHas n (fun (t : A' ⊕ B') (s : A ⊕ B) => SumR A A' pa.R B B' pb.R s t)
  | map0,  _,  _  => {}
  | map1,  pa, pb => { map := Sum.map pa.contra.map pb.contra.map }
  | map2a, pa, pb => { map := Sum.map pa.contra.map pb.contra.map,
                       mapInR := sumContraMapInR pa.contra.map pb.contra.map pa.contra.mapInR pb.contra.mapInR }
  | map2b, pa, pb => { map := Sum.map pa.contra.map pb.contra.map,
                       rInMap := sumContraRInMap pa.contra.map pb.contra.map pa.contra.rInMap pb.contra.rInMap }
  | map3,  pa, pb => { map := Sum.map pa.contra.map pb.contra.map,
                       mapInR := sumContraMapInR pa.contra.map pb.contra.map pa.contra.mapInR pb.contra.mapInR,
                       rInMap := sumContraRInMap pa.contra.map pb.contra.map pa.contra.rInMap pb.contra.rInMap }
  | map4,  pa, pb => { map := Sum.map pa.contra.map pb.contra.map,
                       mapInR := sumContraMapInR pa.contra.map pb.contra.map pa.contra.mapInR pb.contra.mapInR,
                       rInMap := sumContraRInMap pa.contra.map pb.contra.map pa.contra.rInMap pb.contra.rInMap,
                       rInMapK := fun _ _ _ => SumR.allEq (fun a a' => (pa.contra.subsingleton a' a).allEq)
                         (fun b b' => (pb.contra.subsingleton b' b).allEq) _ _ }

/-- `A ⊕ B ≃ A' ⊕ B'` at ANY output class `(m,n)`, each summand at the `sumVariance`-minimal class. -/
@[trocq] noncomputable def paramSum (m n : MapClass) (A A' : Type)
    (pa : Param (sumVariance (m, n)).1 (sumVariance (m, n)).2 A A')
    (B B' : Type)
    (pb : Param (sumVariance (m, n)).1 (sumVariance (m, n)).2 B B') :
    Param m n (A ⊕ B) (A' ⊕ B') where
  R := SumR A A' pa.R B B' pb.R
  cov := sumCov m (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (pb.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := sumContra n (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (pb.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

end LeTrocq.Lib
