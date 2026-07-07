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
`u (f x) = x` / `f (u x) = x`. Its carrier variance is PARAMETRIC, like the other relators (`mapGroupVariance`
/`groupVariance`): the round-trips floor the carrier at `(3,3)` from `map1` up (a plain functor would be the
identity `(c, map0)`), and only the coherence (`map4`) adds `map4` on one slot for the carrier subsingleton.
So a partial `(3,3)` base transports a group at any output up to `map3`, and `(4,4)` is forced only when both
directions want the coherence. The tests instantiate at a concrete `Bool ≃ Parity` (the group ℤ/2ℤ).
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

/- ===================== the equivalence round-trips (from a `map3` carrier) ===================== -/
/- The transport must move the AXIOM proofs, and each axiom reduces via the two round-trips `u (f x) = x` /
   `f (u x) = x`. Those need `mapInR` AND `rInMap` in BOTH directions — i.e. carrier `(map3, map3)`. So a group's
   forward map already floors the carrier at `(3,3)` (not the identity variance of a plain functor). -/
/-- `u ∘ f = id`. -/
theorem bwdFwd {A A' : Type} (pa : Param map3 map3 A A') : ∀ x, pa.contra.map (pa.cov.map x) = x :=
  fun x => pa.contra.rInMap (pa.cov.map x) x (pa.cov.mapInR x (pa.cov.map x) rfl)

/-- `f ∘ u = id`. -/
theorem fwdBwd {A A' : Type} (pa : Param map3 map3 A A') : ∀ y, pa.cov.map (pa.contra.map y) = y :=
  fun y => pa.cov.rInMap (pa.contra.map y) y (pa.contra.mapInR y (pa.contra.map y) rfl)

/- ===================== transporting a group across the carrier equivalence ===================== -/
/-- the transport `Group A → Group A'` from RAW carrier maps `f`/`u` and their round-trips (raw, so no `Param`
    class is baked in — the graded arms feed it the maps at whatever class they hold). The contra half reuses
    this with the maps swapped (`Group A' → Group A`). -/
def groupFwd {A A' : Type} (f : A → A') (u : A' → A)
    (uf : ∀ x, u (f x) = x) (fu : ∀ y, f (u y) = y) (g : Group A) : Group A' where
  mul a' b' := f (g.mul (u a') (u b'))
  one := f g.one
  inv a' := f (g.inv (u a'))
  mul_assoc := by intro a' b' c'; simp only [uf, g.mul_assoc]
  one_mul := by intro a'; simp only [uf, g.one_mul, fu]
  inv_mul := by intro a'; simp only [uf, g.inv_mul]

/- ===================== the two halves at the `(3,3)` carrier floor ===================== -/
/-- covariant half up to `map3`: the transport `groupFwd f u` is sound and complete onto `GroupR`. -/
def groupCov3 {A A' : Type} (pa : Param map3 map3 A A') : Map3Has (GroupR A A' pa.R) where
  map := groupFwd pa.cov.map pa.contra.map (bwdFwd pa) (fwdBwd pa)
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
    have hm : (groupFwd pa.cov.map pa.contra.map (bwdFwd pa) (fwdBwd pa) g).mul = m' := by
      funext a' b'
      exact pa.cov.rInMap _ _ (r.mulR (pa.contra.map a') a' (pa.contra.mapInR a' _ rfl)
                                       (pa.contra.map b') b' (pa.contra.mapInR b' _ rfl))
    have ho : (groupFwd pa.cov.map pa.contra.map (bwdFwd pa) (fwdBwd pa) g).one = o' := pa.cov.rInMap _ _ r.oneR
    have hi : (groupFwd pa.cov.map pa.contra.map (bwdFwd pa) (fwdBwd pa) g).inv = i' := by
      funext a'
      exact pa.cov.rInMap _ _ (r.invR (pa.contra.map a') a' (pa.contra.mapInR a' _ rfl))
    subst hm; subst ho; subst hi; rfl

/-- contravariant half up to `map3` (the mirror: `groupFwd` with the maps swapped, `Group A' → Group A`). -/
def groupContra3 {A A' : Type} (pa : Param map3 map3 A A') :
    Map3Has (fun (g' : Group A') (g : Group A) => GroupR A A' pa.R g g') where
  map := groupFwd pa.contra.map pa.cov.map (fwdBwd pa) (bwdFwd pa)
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
    have hm : (groupFwd pa.contra.map pa.cov.map (fwdBwd pa) (bwdFwd pa) g').mul = m := by
      funext a b
      exact pa.contra.rInMap _ _ (r.mulR a (pa.cov.map a) (pa.cov.mapInR a _ rfl)
                                         b (pa.cov.map b) (pa.cov.mapInR b _ rfl))
    have ho : (groupFwd pa.contra.map pa.cov.map (fwdBwd pa) (bwdFwd pa) g').one = o := pa.contra.rInMap _ _ r.oneR
    have hi : (groupFwd pa.contra.map pa.cov.map (fwdBwd pa) (bwdFwd pa) g').inv = i := by
      funext a
      exact pa.contra.rInMap _ _ (r.invR a (pa.cov.map a) (pa.cov.mapInR a _ rfl))
    subst hm; subst ho; subst hi; rfl

/- ===================== the variance table + the graded relator ===================== -/
/-- per-map-class minimal carrier class for `Group`. Because the forward map transports the axioms via the
    round-trips, the floor is `(3,3)` from `map1` up; `map4` adds `map4` on the cov slot for the coherence's
    carrier subsingleton. -/
def mapGroupVariance : MapClass → ParamClass
  | map0  => (map0, map0)
  | map1  => (map3, map3)
  | map2a => (map3, map3)
  | map2b => (map3, map3)
  | map3  => (map3, map3)
  | map4  => (map4, map3)

/-- minimal carrier class to build `Group` at output class `c` (cov joined with negated contra). -/
def groupVariance (c : ParamClass) : ParamClass :=
  ParamClass.join (mapGroupVariance c.1) (ParamClass.negate (mapGroupVariance c.2))

/-- the covariant half at ANY output class: build the `map3` witness and forget down; at `map4` add the
    coherence (its carrier subsingleton comes from `pa.cov` at `map4`). -/
def groupCov {A A' : Type} :
    (m : MapClass) → (pa : Param (mapGroupVariance m).1 (mapGroupVariance m).2 A A') →
    MapHas m (GroupR A A' pa.R)
  | map0,  _  => {}
  | map1,  pa => MapClass.forget2a1 (MapClass.forget32a (groupCov3 pa))
  | map2a, pa => MapClass.forget32a (groupCov3 pa)
  | map2b, pa => MapClass.forget32b (groupCov3 pa)
  | map3,  pa => groupCov3 pa
  | map4,  pa =>
      let c := groupCov3 (pa.weaken (by decide) (by decide))
      { map := c.map, mapInR := c.mapInR, rInMap := c.rInMap,
        rInMapK := fun _ _ _ => GroupR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq) _ _ }

/-- the contravariant half at ANY output class (mirror; at `map4` the subsingleton comes from `pa.contra`). -/
def groupContra {A A' : Type} :
    (n : MapClass) → (pa : Param (mapGroupVariance n).2 (mapGroupVariance n).1 A A') →
    MapHas n (fun (g' : Group A') (g : Group A) => GroupR A A' pa.R g g')
  | map0,  _  => {}
  | map1,  pa => MapClass.forget2a1 (MapClass.forget32a (groupContra3 pa))
  | map2a, pa => MapClass.forget32a (groupContra3 pa)
  | map2b, pa => MapClass.forget32b (groupContra3 pa)
  | map3,  pa => groupContra3 pa
  | map4,  pa =>
      let c := groupContra3 (pa.weaken (by decide) (by decide))
      { map := c.map, mapInR := c.mapInR, rInMap := c.rInMap,
        rInMapK := fun _ _ _ => GroupR.allEq (fun a a' => (pa.contra.subsingleton a' a).allEq) _ _ }

/-- `Group A ≃ Group A'` at ANY output class `(m,n)`, the carrier at the `groupVariance`-minimal class. Unlike
    the old fixed-`(4,4)` version, the carrier demand now SCALES with the output — a `(3,3)` base transports a
    group at any output up to `map3` (`(4,4)` is only forced when both output directions want the coherence). -/
@[trocq] def paramGroup (m n : MapClass) (A A' : Type)
    (pa : Param (groupVariance (m, n)).1 (groupVariance (m, n)).2 A A') :
    Param m n (Group A) (Group A') where
  R := GroupR A A' pa.R
  cov := groupCov m (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := groupContra n (pa.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

end LeTrocq.Examples
