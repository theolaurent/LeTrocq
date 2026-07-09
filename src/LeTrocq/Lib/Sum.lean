/-
`Sum` (⊕, disjoint union) — two type parameters (like `Prod`) but two constructors (like `Option`). `SumR` is
the parametricity relation (`inl ~ inl`, `inr ~ inr`); its constructors auto-register as the `Sum.inl`/`Sum.inr`
term primitives; `paramSum` is the graded relator (variance parallel to `List`; forward map is `Sum.map`).
-/
import LeTrocq.Driver.Registry
namespace LeTrocq.Lib
open LeTrocq MapClass

/-- two sums are related iff they take the same injection with componentwise-related payloads. -/
@[trocq] inductive SumR (A A' : Type) (RA : A → A' → Type) (B B' : Type) (RB : B → B' → Type) :
    A ⊕ B → A' ⊕ B' → Type
  | inl {a a'} (aRel : RA a a') : SumR A A' RA B B' RB (.inl a) (.inl a')
  | inr {b b'} (bRel : RB b b') : SumR A A' RA B B' RB (.inr b) (.inr b')

/-- the relation is a subsingleton whenever both summand relations are — needed for the `(4,4)` coherence. -/
theorem SumR.allEq {A A' : Type} {RA : A → A' → Type} {B B' : Type} {RB : B → B' → Type}
    (hA : ∀ a a' (x y : RA a a'), x = y) (hB : ∀ b b' (x y : RB b b'), x = y) :
    {s : A ⊕ B} → {t : A' ⊕ B'} → (x y : SumR A A' RA B B' RB s t) → x = y
  | _, _, .inl aRel, .inl aRel' => by rw [hA _ _ aRel aRel']
  | _, _, .inr bRel, .inr bRel' => by rw [hB _ _ bRel bRel']

/- `SumR.inl`/`SumR.inr` auto-register as the `Sum.inl`/`Sum.inr` term primitives (tagging `SumR`). -/

/- ===================== the graded relator (variance parallel to `paramList`) =====================
   `Sum` is a covariant functor in both summands (identity variance): each summand is needed at exactly the
   output class. -/

/-- minimal class per direction of each summand of `Sum` (pure covariance; same table for both). -/
def mapSumVariance : MapClass → ParamClass
  | map0  => (map0,  map0)
  | map1  => (map1,  map0)
  | map2a => (map2a, map0)
  | map2b => (map2b, map0)
  | map3  => (map3,  map0)
  | map4  => (map4,  map0)

/-- per-summand class to build `Sum` at output class `c` (identity, via the shared `ParamClass.variance`). -/
def sumVariance (c : ParamClass) : ParamClass := ParamClass.variance mapSumVariance c

/-- soundness `SumR` from `Sum.map f g`, shared by the `2a`/`3`/`4` arms. -/
def sumMapInR {A A' B B' : Type} {RA : A → A' → Type} {RB : B → B' → Type} (f : A → A') (g : B → B')
    (fInR : ∀ a a', f a = a' → RA a a') (gInR : ∀ b b', g b = b' → RB b b') :
    ∀ s t, Sum.map f g s = t → SumR A A' RA B B' RB s t :=
  fun s _ h => by subst h; cases s with
    | inl a => exact .inl (fInR a _ rfl)
    | inr b => exact .inr (gInR b _ rfl)

/-- completeness `Sum.map f g` from `SumR`, shared by the `2b`/`3`/`4` arms. -/
theorem sumRInMap {A A' B B' : Type} {RA : A → A' → Type} {RB : B → B' → Type} (f : A → A') (g : B → B')
    (fRInMap : ∀ a a', RA a a' → f a = a') (gRInMap : ∀ b b', RB b b' → g b = b') :
    ∀ s t, SumR A A' RA B B' RB s t → Sum.map f g s = t :=
  fun _ _ r => by cases r with
    | inl aRel => exact congrArg Sum.inl (fRInMap _ _ aRel)
    | inr bRel => exact congrArg Sum.inr (gRInMap _ _ bRel)

/-- contra soundness, the mirror of `sumMapInR`. -/
def sumContraMapInR {A A' B B' : Type} {RA : A → A' → Type} {RB : B → B' → Type} (f : A' → A) (g : B' → B)
    (fInR : ∀ a' a, f a' = a → RA a a') (gInR : ∀ b' b, g b' = b → RB b b') :
    ∀ t s, Sum.map f g t = s → SumR A A' RA B B' RB s t :=
  fun t _ h => by subst h; cases t with
    | inl a => exact .inl (fInR a _ rfl)
    | inr b => exact .inr (gInR b _ rfl)

/-- contra completeness, the mirror of `sumRInMap`. -/
theorem sumContraRInMap {A A' B B' : Type} {RA : A → A' → Type} {RB : B → B' → Type} (f : A' → A) (g : B' → B)
    (fRInMap : ∀ a' a, RA a a' → f a' = a) (gRInMap : ∀ b' b, RB b b' → g b' = b) :
    ∀ t s, SumR A A' RA B B' RB s t → Sum.map f g t = s :=
  fun _ _ r => by cases r with
    | inl aRel => exact congrArg Sum.inl (fRInMap _ _ aRel)
    | inr bRel => exact congrArg Sum.inr (gRInMap _ _ bRel)

/-- the covariant half from the two summands at `mapSumVariance m`; the `map4` coherence is free (subsingleton). -/
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
