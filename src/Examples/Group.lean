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

The parametricity relation `GroupR` is a `structure` relating the three OPERATIONS (a homomorphism of the
signature). Tagging it `@[trocq]` auto-registers `Group.mul`/`Group.one`/`Group.inv` as term primitives (the
projection fields are already in triple form) — with NO hand-written proxy. `GroupR` relates 3 of `Group`'s 6
fields, so the constructor `Group.mk` is NOT auto-built (the field counts differ — you transport a group
wholesale via `paramGroup`, not term-by-term); its projections are what matter.

`paramGroup` (the graded relator for `trocq`/`transfer%`) is hand-written, transporting a WHOLE group across a
carrier equivalence `A ≃ A'` — including the axiom proofs, discharged by the equivalence round-trips
`u (f x) = x` / `f (u x) = x`. A group needs the full `(4,4)` carrier equivalence (the operations move both
ways), so — like `paramEq` — its carrier argument is fixed at `(4,4)` and the witness is built there and
weakened to the demanded output class. The tests instantiate at a concrete `Bool ≃ Parity` (the group ℤ/2ℤ).
-/
import LeTrocq
namespace LeTrocq.Examples
open LeTrocq MapClass

/- ===================== the group structure and its signature relation ===================== -/
structure Group (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  inv_mul : ∀ a, mul (inv a) a = one

/-- two groups are related iff their OPERATIONS correspond (a homomorphism of the signature). A STRUCTURE
    relation: tagging it auto-registers `Group.mul`/`Group.one`/`Group.inv` as term primitives. -/
@[trocq] structure GroupR (A A' : Type) (RA : A → A' → Type) (g : Group A) (g' : Group A') where
  mulR : ∀ a a', RA a a' → ∀ b b', RA b b' → RA (g.mul a b) (g'.mul a' b')
  oneR : RA g.one g'.one
  invR : ∀ a a', RA a a' → RA (g.inv a) (g'.inv a')

/-- the relation is a subsingleton when the carrier relation is — needed for the `(4,4)` coherence. -/
theorem GroupR.allEq {A A' : Type} {RA : A → A' → Type} (hR : ∀ a a' (x y : RA a a'), x = y)
    {g : Group A} {g' : Group A'} (u v : GroupR A A' RA g g') : u = v := by
  cases u with | mk um uo ui => cases v with | mk vm vo vi =>
  have e1 : um = vm := by funext a a' aR b b' bR; exact hR _ _ _ _
  have e2 : uo = vo := hR _ _ _ _
  have e3 : ui = vi := by funext a a' aR; exact hR _ _ _ _
  subst e1; subst e2; subst e3; rfl

/- ===================== the equivalence round-trips (from a `(4,4)` carrier) ===================== -/
/-- `u ∘ f = id`: composing the forward then backward carrier map is the identity. -/
theorem bwdFwd {A A' : Type} (pa : Param map4 map4 A A') (x : A) :
    pa.contra.map (pa.cov.map x) = x :=
  pa.contra.rInMap (pa.cov.map x) x (pa.cov.mapInR x (pa.cov.map x) rfl)

/-- `f ∘ u = id`: the other round-trip. -/
theorem fwdBwd {A A' : Type} (pa : Param map4 map4 A A') (y : A') :
    pa.cov.map (pa.contra.map y) = y :=
  pa.cov.rInMap (pa.contra.map y) y (pa.contra.mapInR y (pa.contra.map y) rfl)

/- ===================== transporting a group across the carrier equivalence ===================== -/
/-- the forward transport `Group A → Group A'`: conjugate each operation by the equivalence (`f ∘ op ∘ u`), and
    move each axiom over via the round-trips. -/
def groupMap {A A' : Type} (pa : Param map4 map4 A A') (g : Group A) : Group A' where
  mul a' b' := pa.cov.map (g.mul (pa.contra.map a') (pa.contra.map b'))
  one := pa.cov.map g.one
  inv a' := pa.cov.map (g.inv (pa.contra.map a'))
  mul_assoc := by intro a' b' c'; simp only [bwdFwd, g.mul_assoc]
  one_mul := by intro a'; simp only [bwdFwd, g.one_mul, fwdBwd]
  inv_mul := by intro a'; simp only [bwdFwd, g.inv_mul]

/-- the backward transport `Group A' → Group A` (the mirror, `u ∘ op ∘ f`). -/
def groupComap {A A' : Type} (pa : Param map4 map4 A A') (g' : Group A') : Group A where
  mul a b := pa.contra.map (g'.mul (pa.cov.map a) (pa.cov.map b))
  one := pa.contra.map g'.one
  inv a := pa.contra.map (g'.inv (pa.cov.map a))
  mul_assoc := by intro a b c; simp only [fwdBwd, g'.mul_assoc]
  one_mul := by intro a; simp only [fwdBwd, g'.one_mul, bwdFwd]
  inv_mul := by intro a; simp only [fwdBwd, g'.inv_mul]

/- ===================== the relator, at the `(4,4)` carrier ===================== -/
/-- the covariant half: the transport `groupMap` is an equivalence onto `GroupR`. -/
def groupCov {A A' : Type} (pa : Param map4 map4 A A') : Map4Has (GroupR A A' pa.R) where
  map := groupMap pa
  mapInR := by
    intro g g' h; subst h
    refine ⟨fun a a' aR b b' bR => ?_, pa.cov.mapInR _ _ rfl, fun a a' aR => ?_⟩
    · show pa.R (g.mul a b) (pa.cov.map (g.mul (pa.contra.map a') (pa.contra.map b')))
      rw [pa.contra.rInMap a' a aR, pa.contra.rInMap b' b bR]; exact pa.cov.mapInR _ _ rfl
    · show pa.R (g.inv a) (pa.cov.map (g.inv (pa.contra.map a')))
      rw [pa.contra.rInMap a' a aR]; exact pa.cov.mapInR _ _ rfl
  rInMap := by
    intro g g' r
    obtain ⟨m', o', i', ax1, ax2, ax3⟩ := g'
    have hm : (groupMap pa g).mul = m' := by
      funext a' b'
      exact pa.cov.rInMap _ _ (r.mulR (pa.contra.map a') a' (pa.contra.mapInR a' _ rfl)
                                       (pa.contra.map b') b' (pa.contra.mapInR b' _ rfl))
    have ho : (groupMap pa g).one = o' := pa.cov.rInMap _ _ r.oneR
    have hi : (groupMap pa g).inv = i' := by
      funext a'
      exact pa.cov.rInMap _ _ (r.invR (pa.contra.map a') a' (pa.contra.mapInR a' _ rfl))
    subst hm; subst ho; subst hi; rfl
  rInMapK := fun _ _ _ => GroupR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq) _ _

/-- the contravariant half (the mirror, over `groupComap`). -/
def groupContra {A A' : Type} (pa : Param map4 map4 A A') :
    Map4Has (fun (g' : Group A') (g : Group A) => GroupR A A' pa.R g g') where
  map := groupComap pa
  mapInR := by
    intro g' g h; subst h
    refine ⟨fun a a' aR b b' bR => ?_, pa.contra.mapInR _ _ rfl, fun a a' aR => ?_⟩
    · show pa.R (pa.contra.map (g'.mul (pa.cov.map a) (pa.cov.map b))) (g'.mul a' b')
      rw [pa.cov.rInMap a a' aR, pa.cov.rInMap b b' bR]; exact pa.contra.mapInR _ _ rfl
    · show pa.R (pa.contra.map (g'.inv (pa.cov.map a))) (g'.inv a')
      rw [pa.cov.rInMap a a' aR]; exact pa.contra.mapInR _ _ rfl
  rInMap := by
    intro g' g r
    obtain ⟨m, o, i, ax1, ax2, ax3⟩ := g
    have hm : (groupComap pa g').mul = m := by
      funext a b
      exact pa.contra.rInMap _ _ (r.mulR a (pa.cov.map a) (pa.cov.mapInR a _ rfl)
                                         b (pa.cov.map b) (pa.cov.mapInR b _ rfl))
    have ho : (groupComap pa g').one = o := pa.contra.rInMap _ _ r.oneR
    have hi : (groupComap pa g').inv = i := by
      funext a
      exact pa.contra.rInMap _ _ (r.invR a (pa.cov.map a) (pa.cov.mapInR a _ rfl))
    subst hm; subst ho; subst hi; rfl
  rInMapK := fun _ _ _ => GroupR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq) _ _

/-- `Group A ≃ Group A'` at the `(4,4)` carrier equivalence. -/
def paramGroup44 {A A' : Type} (pa : Param map4 map4 A A') : Param map4 map4 (Group A) (Group A') where
  R := GroupR A A' pa.R
  cov := groupCov pa
  contra := groupContra pa

/-- `Group A ≃ Group A'` at ANY output class `(m,n)`, from the `(4,4)` carrier (the operations move both ways,
    so a group cannot transport across a weaker carrier — the carrier stays fixed at `(4,4)`, like `paramEq`). -/
@[trocq] def paramGroup (m n : MapClass) (A A' : Type) (pa : Param map4 map4 A A') :
    Param m n (Group A) (Group A') :=
  (paramGroup44 pa).weaken (MapClass.le_map4 m) (MapClass.le_map4 n)

end LeTrocq.Examples
