/-
A registered STRUCTURE (record): a GROUP (the mathematical structure).

The prelude relations (`List`/`Sigma`/…) are INDUCTIVEs, consumed by their CONSTRUCTORS; a record type is
consumed by its FIELD PROJECTIONS, so its natural relation is a `structure` whose fields relate the
projections. `@[trocq]` on such a structure auto-registers each projection as a term primitive (a structure
field is already in abstraction-theorem triple form, so no proxy). A group exercises the full range of
structure fields:
  • FUNCTION fields — `mul : G → G → G`, `inv : G → G`;
  • a CONSTANT field — `one : G`;
  • PROP (axiom) fields — `mul_assoc`/`one_mul`/`inv_mul`.

The parametricity relation `GroupR` is a `class` relating the three OPERATIONS (a homomorphism of the
signature). Tagging it `@[trocq]` auto-registers `Group.mul`/`Group.one`/`Group.inv` as term primitives (the
projection fields are already in triple form) — with NO hand-written proxy.

We then use `GroupR` for its own sake: to relate TWO DISTINCT, non-isomorphic group instances —
`intGroup` (ℤ) and `boolGroup` (ℤ/2ℤ) — through the parity homomorphism ℤ ↠ ℤ/2ℤ. This is NOT a transport
across a type equivalence (`Int` and `Bool` are not equivalent types); it is a standalone correspondence
witness. Tagging it `@[trocq]` registers `intGroup ↦ boolGroup` as a term primitive, and the partial parity
carrier `RBI : Param map4 map2a Int Bool` lets `trocq` cross `Int`/`Bool` elements (see `Tests/Driver/Group`).
-/
import LeTrocq
namespace LeTrocq.Examples
open LeTrocq MapClass

/- ===================== the group typeclass and its signature relation ===================== -/
/-- the mathematical structure of a group, as a `class` (a Lean typeclass: `[Group G]` is "G is a group"). -/
class Group (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  inv_mul : ∀ a, mul (inv a) a = one

/-- two group instances are related iff their OPERATIONS correspond (a homomorphism of the signature). The
    relation is itself a `@[trocq] class` — its projections auto-register `Group.mul`/`Group.one`/`Group.inv`
    as term primitives, and a concrete correspondence registers as a `@[trocq] instance` (see the tests). Only
    the DRIVER consumes it (by head-lookup in the `@[trocq]` registry, never `synthInstance`), so making it a
    class is just for the class/instance parallelism — `paramGroup` below stays a plain `def`. -/
@[trocq] class GroupR (A A' : Type) (RA : A → A' → Type) (g : Group A) (g' : Group A') where
  mulR : ∀ a a', RA a a' → ∀ b b', RA b b' → RA (g.mul a b) (g'.mul a' b')
  oneR : RA g.one g'.one
  invR : ∀ a a', RA a a' → RA (g.inv a) (g'.inv a')

/- ===================== two concrete groups + their correspondence ===================== -/
/-- ℤ/2ℤ on `Bool` (`mul = xor`, `one = false`, `inv = id`); laws by `decide`. -/
instance boolGroup : Group Bool where
  mul a b := a != b
  one := false
  inv a := a
  mul_assoc := by decide
  one_mul := by decide
  inv_mul := by decide

/-- ℤ on `Int` (`mul = +`, `one = 0`, `inv = -·`); laws by `omega`. -/
instance intGroup : Group Int where
  mul a b := a + b
  one := 0
  inv a := -a
  mul_assoc := by intro a b c; omega
  one_mul := by intro a; omega
  inv_mul := by intro a; omega

/-- relate an `Int` (ℤ) to a `Bool` (ℤ/2ℤ) by PARITY: `z` corresponds to `b` when `z`'s parity is `b`
    (Lean's Euclidean `%` gives `z % 2 ∈ {0,1}`, so this is well-defined). Oriented `Int`-FIRST, so an
    `Int`-side `trocq` goal crosses forward (the goal side is the `A` side — no `sym` needed). -/
def parityR (z : Int) (b : Bool) : Type := PLift (z % 2 = bif b then 1 else 0)

/-- `intGroup` and `boolGroup` CORRESPOND under parity — the group homomorphism ℤ ↠ ℤ/2ℤ, as a `GroupR`
    witness relating two DISTINCT (non-isomorphic) group instances. Tagged `@[trocq]`, so the driver
    registers `intGroup ↦ boolGroup` as a term primitive. (`simp only … at h1 h2 ⊢` reduces the `cond`/`bne`
    without weaponizing the mod hypotheses away from `omega`, which `simp_all` would.) -/
@[trocq] def intBoolGroupR : GroupR Int Bool parityR intGroup boolGroup where
  mulR z z' hz w w' hw := ⟨by
    have h1 := hz.down; have h2 := hw.down
    cases z' <;> cases w' <;>
      simp only [boolGroup, intGroup, cond_true, cond_false, Bool.true_bne, Bool.false_bne,
        Bool.not_true, Bool.not_false] at h1 h2 ⊢ <;> omega⟩
  oneR := ⟨by decide⟩
  invR z z' hz := ⟨by
    have h := hz.down
    cases z' <;> simp only [boolGroup, intGroup, cond_true, cond_false] at h ⊢ <;> omega⟩

/- ===================== the parity CARRIER as a partial `Param` ===================== -/
/-- the parity relation packaged as a `Param Int Bool`: only PARTIAL. The `Int → Bool` parity map is a full
    retraction (map4), but the `Bool → Int` section `bif b then 1 else 0` is SOUND (2a) and not complete
    (many ints per bool). So the carrier tops out at `(4, 2a)` — exactly the soundness boundary of the
    non-injective quotient ℤ ↠ ℤ/2ℤ: it lets `trocq` cross `Int`/`Bool` ELEMENTS, but not transport
    equations that would need the missing `Bool → Int` completeness. -/
@[trocq] def RBI : Param map4 map2a Int Bool where
  R := parityR
  cov :=
    { map := fun z => z % 2 != 0
      mapInR := fun z b h => ⟨by
        subst h; rcases (show z % 2 = 0 ∨ z % 2 = 1 by omega) with h | h <;> rw [h] <;> decide⟩
      rInMap := fun z b r => by
        have h := r.down; cases b <;> simp only [cond_true, cond_false] at h <;> rw [h] <;> decide
      rInMapK := fun _ _ _ => rfl }
  contra :=
    { map := fun b => bif b then 1 else 0
      mapInR := fun b z h => ⟨by subst h; cases b <;> decide⟩ }

end LeTrocq.Examples
