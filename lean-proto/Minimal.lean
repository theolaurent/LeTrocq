/-
MINIMAL WORKING EXAMPLE of Trocq-style proof transfer in Lean 4.

Punchline (the paper's flagship, minimised): we register an isomorphism between `Nat` and a custom
unary type `Unary` as a `Param (4,4)` witness, and then obtain `Unary`'s induction principle FOR FREE
from `Nat`'s recursor — the transport being carried entirely by the `Param` hierarchy's projections.
`#print axioms` at the end shows the result uses no univalence (indeed no axioms at all).

Self-contained; core Lean only.
-/

universe u v
namespace Trocq

/- ======================================================================================
   1. The hierarchy (the validated encoding from Defeq.lean, full six levels).
   ====================================================================================== -/
inductive MapClass | mZero | mOne | mTwoA | mTwoB | mThree | mFour deriving DecidableEq, Repr
abbrev ParamClass := MapClass × MapClass

structure Map0Has {A B : Type u} (_R : A → B → Type v) : Type u where
structure Map1Has {A B : Type u} (_R : A → B → Type v) : Type u where
  map : A → B
structure Map2aHas {A B : Type u} (R : A → B → Type v) where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
structure Map2bHas {A B : Type u} (R : A → B → Type v) : Type u where
  map : A → B
  R_in_map : ∀ a b, R a b → map a = b
structure Map3Has {A B : Type u} (R : A → B → Type v) where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
  R_in_map : ∀ a b, R a b → map a = b
structure Map4Has {A B : Type u} (R : A → B → Type v) where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
  R_in_map : ∀ a b, R a b → map a = b
  R_in_mapK : ∀ a b r, map_in_R a b (R_in_map a b r) = r

def MapHas : MapClass → {A B : Type u} → (A → B → Type v) → Type (max u v)
  | .mZero,  _, _, R => ULift.{v} (Map0Has R)
  | .mOne,   _, _, R => ULift.{v} (Map1Has R)
  | .mTwoA,  _, _, R => Map2aHas R
  | .mTwoB,  _, _, R => ULift.{v} (Map2bHas R)
  | .mThree, _, _, R => Map3Has R
  | .mFour,  _, _, R => Map4Has R

structure Param (m n : MapClass) (A B : Type u) where
  R      : A → B → Type v
  cov    : MapHas m R
  contra : MapHas n (fun b a => R a b)

/- Projections we need at class (4,4): the two transport functions and BOTH round-trips,
   all derived generically from the record fields (this is what makes the transfer "free"). -/
namespace Param
variable {A B : Type u}
abbrev P44 (A B : Type u) := Param.{u, v} .mFour .mFour A B

/-- forward transport `A → B` -/
def f (P : P44 A B) : A → B := P.cov.map
/-- backward transport `B → A` -/
def g (P : P44 A B) : B → A := P.contra.map

/-- `f (g b) = b`, recovered from the covariant `R_in_map` ∘ contravariant `map_in_R`. -/
def fg (P : P44 A B) (b : B) : P.f (P.g b) = b :=
  P.cov.R_in_map (P.contra.map b) b (P.contra.map_in_R b (P.contra.map b) rfl)
/-- `g (f a) = a`, the dual. -/
def gf (P : P44 A B) (a : A) : P.g (P.f a) = a :=
  P.contra.R_in_map (P.cov.map a) a (P.cov.map_in_R a (P.cov.map a) rfl)
end Param

/- ======================================================================================
   2. THE GENERIC TRANSFER LEMMA. Given any (4,4) relation between A and B, plus the fact
      that B's "zero/succ" correspond to A's, transport A's induction principle to B.
      This is exactly the term Trocq's translation would synthesise for this goal.
   ====================================================================================== -/
theorem transfer_induction {A B : Type}
    (P : Param.{0,0} .mFour .mFour A B)
    (zA : A) (sA : A → A)
    (Arec : ∀ (Pr : A → Prop), Pr zA → (∀ a, Pr a → Pr (sA a)) → ∀ a, Pr a)
    (zB : B) (sB : B → B)
    (hz : P.g zB = zA)                              -- "0 is related to zero"
    (hs : ∀ b, P.g (sB b) = sA (P.g b)) :           -- "succ is related to succ"
    ∀ (Q : B → Prop), Q zB → (∀ b, Q b → Q (sB b)) → ∀ b, Q b := by
  intro Q qz qs
  -- transported predicate on A:  Pr a := Q (f a)
  have base : ∀ a, Q (P.f a) := by
    refine Arec (fun a => Q (P.f a)) ?_ ?_
    · -- Q (f zA);  f zA = f (g zB) = zB
      show Q (P.f zA)
      have : P.f zA = zB := by rw [← hz]; exact P.fg zB
      rw [this]; exact qz
    · -- step:  Q (f a) → Q (f (sA a))
      intro a ih
      show Q (P.f (sA a))
      -- f (sA a) = sB (f a):  apply f to  g (sB (f a)) = sA (g (f a)) = sA a
      have e1 : P.g (sB (P.f a)) = sA a := by rw [hs, P.gf]
      have e2 : P.f (sA a) = sB (P.f a) := by rw [← e1]; exact P.fg _
      rw [e2]; exact qs _ ih
  -- pull back along  f (g b) = b
  intro b
  have := base (P.g b)
  rwa [P.fg b] at this

/- ======================================================================================
   3. THE CONCRETE INSTANCE: register  Nat ≃ Unary  as a Param (4,4).
   ====================================================================================== -/
inductive Unary | z | s (n : Unary) deriving Repr

def toNat : Unary → Nat | .z => 0 | .s n => toNat n + 1
def ofNat : Nat → Unary | 0 => .z | n+1 => .s (ofNat n)

theorem toNat_ofNat : ∀ n, toNat (ofNat n) = n
  | 0 => rfl
  | n+1 => by show toNat (ofNat n) + 1 = n + 1; rw [toNat_ofNat n]
theorem ofNat_toNat : ∀ u, ofNat (toNat u) = u
  | .z => rfl
  | .s n => by show Unary.s (ofNat (toNat n)) = Unary.s n; rw [ofNat_toNat n]

/-- the relation: graph of `toNat` (Prop, lifted to `Type` so it fits `R : _ → _ → Type`). -/
def RNU : Nat → Unary → Type := fun n u => PLift (toNat u = n)

/-- the registered (4,4) witness — the only thing the user proves by hand. -/
def RN : Param.{0,0} .mFour .mFour Nat Unary where
  R := RNU
  cov :=
    { map := ofNat
      map_in_R := fun n u h => PLift.up (by subst h; exact toNat_ofNat n)
      R_in_map := fun n u r => by have h := r.down; rw [← h, ofNat_toNat]
      R_in_mapK := fun _ _ _ => rfl }       -- free: PLift of a Prop, definitional proof irrelevance
  contra :=
    { map := toNat
      map_in_R := fun u n h => PLift.up h
      R_in_map := fun u n r => r.down
      R_in_mapK := fun _ _ _ => rfl }

/- ======================================================================================
   4. THE PAYOFF: Unary's induction principle, obtained FOR FREE from `Nat.rec`.
   ====================================================================================== -/
theorem Unary.induction :
    ∀ (Q : Unary → Prop), Q .z → (∀ u, Q u → Q (.s u)) → ∀ u, Q u :=
  transfer_induction RN
    (zA := 0) (sA := Nat.succ)
    (Arec := fun Pr h0 hs => @Nat.rec Pr h0 hs)
    (zB := .z) (sB := .s)
    (hz := rfl)                  -- toNat .z = 0
    (hs := fun _ => rfl)         -- toNat (.s b) = Nat.succ (toNat b)

-- It really is a usable induction principle: use it to prove something about Unary.
def Unary.height : Unary → Nat := toNat
example : ∀ u : Unary, 0 ≤ Unary.height u :=
  Unary.induction (fun u => 0 ≤ Unary.height u) (Nat.le_refl 0) (fun _ ih => Nat.le_succ_of_le ih)

end Trocq

-- THE CLEANLINESS CHECK: no univalence, in fact no axioms whatsoever.
#print axioms Trocq.Unary.induction
