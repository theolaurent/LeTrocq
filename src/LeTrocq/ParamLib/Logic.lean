/-
The LeTrocq STANDARD LIBRARY: the logical connectives (`Not`, `And`, `Or`, `Iff`).

Each registers as a GRADED relator `⋆ P Q ≃ ⋆ P' Q'` built DIRECTLY at the demanded class `(m,n)` (no
weaken-from-top). A proposition carries no data above class 1 (completeness/coherence are free by proof
irrelevance — `propMapHas`), so a `Prop` PART is only ever demanded up to `meet · map1`: the variance sends
`(0,0) ↦ (0,0)`, `(4,4) ↦ (1,1)`, `(2a,0) ↦ (1,0)`, … `And`/`Or` are covariant in both parts; `Not` is
CONTRAVARIANT (`¬P → ¬P'` runs the part backward), so its variance is negated; `Iff` uses BOTH directions of
each part in each direction of the whole, so its part is needed at `(1,1)` as soon as either output class is ≥ 1.

The relation carried is the trivial `fun _ _ => PLift True` — the `Prop` relatedness `[·]` needs is recovered
by `iffOfParam` off the `cov`/`contra` maps, which is all a proposition transports. The driver knows NO
connective intrinsically: a proposition is a `Sort 0` type, so `assemble` crosses `⋆` by the ordinary relator
lookup, `⟨·⟩` reads its counterpart off the conclusion, and the parts recurse at the variance class.
-/
import LeTrocq.Attr
import LeTrocq.ParamCC.Universe
namespace LeTrocq.ParamLib
open LeTrocq MapClass

/- ===================== variance tables (a `Prop` part is capped at `meet · map1`) ===================== -/
/-- covariant `Prop`-connective part variance (`And`/`Or`): a part is needed up to class 1, free above. -/
def mapPropVariance : MapClass → ParamClass
  | map0 => (map0, map0)
  | _    => (map1, map0)

def propVariance (c : ParamClass) : ParamClass :=
  ParamClass.join (mapPropVariance c.1) (ParamClass.negate (mapPropVariance c.2))

/-- `Not` is contravariant: it needs the part in the mirror direction. -/
def notVariance (c : ParamClass) : ParamClass := propVariance (c.2, c.1)

/-- `Iff` uses both directions of each part in each direction of the whole, so the part is `(1,1)` unless
    the output is `(0,0)`. -/
def mapIffVariance : MapClass → ParamClass
  | map0 => (map0, map0)
  | _    => (map1, map1)

def iffVariance (c : ParamClass) : ParamClass :=
  ParamClass.join (mapIffVariance c.1) (ParamClass.negate (mapIffVariance c.2))

/- ===================== And ===================== -/
def andCov {P P' Q Q' : Prop} :
    (m : MapClass) →
    Param (mapPropVariance m).1 (mapPropVariance m).2 P P' →
    Param (mapPropVariance m).1 (mapPropVariance m).2 Q Q' →
    MapHas m (fun (_ : P ∧ Q) (_ : P' ∧ Q') => PLift True)
  | map0,  _,  _  => {}
  | map1,  PR, QR => propMapHas (fun h => ⟨PR.cov.map h.1, QR.cov.map h.2⟩) map1
  | map2a, PR, QR => propMapHas (fun h => ⟨PR.cov.map h.1, QR.cov.map h.2⟩) map2a
  | map2b, PR, QR => propMapHas (fun h => ⟨PR.cov.map h.1, QR.cov.map h.2⟩) map2b
  | map3,  PR, QR => propMapHas (fun h => ⟨PR.cov.map h.1, QR.cov.map h.2⟩) map3
  | map4,  PR, QR => propMapHas (fun h => ⟨PR.cov.map h.1, QR.cov.map h.2⟩) map4

def andContra {P P' Q Q' : Prop} :
    (n : MapClass) →
    Param (mapPropVariance n).2 (mapPropVariance n).1 P P' →
    Param (mapPropVariance n).2 (mapPropVariance n).1 Q Q' →
    MapHas n (fun (_ : P' ∧ Q') (_ : P ∧ Q) => PLift True)
  | map0,  _,  _  => {}
  | map1,  PR, QR => propMapHas (fun h => ⟨PR.contra.map h.1, QR.contra.map h.2⟩) map1
  | map2a, PR, QR => propMapHas (fun h => ⟨PR.contra.map h.1, QR.contra.map h.2⟩) map2a
  | map2b, PR, QR => propMapHas (fun h => ⟨PR.contra.map h.1, QR.contra.map h.2⟩) map2b
  | map3,  PR, QR => propMapHas (fun h => ⟨PR.contra.map h.1, QR.contra.map h.2⟩) map3
  | map4,  PR, QR => propMapHas (fun h => ⟨PR.contra.map h.1, QR.contra.map h.2⟩) map4

@[trocq] def paramAndR (m n : MapClass) (P P' : Prop)
    (PR : Param (propVariance (m, n)).1 (propVariance (m, n)).2 P P')
    (Q Q' : Prop) (QR : Param (propVariance (m, n)).1 (propVariance (m, n)).2 Q Q') :
    Param m n (P ∧ Q) (P' ∧ Q') where
  R := fun _ _ => PLift True
  cov := andCov m (PR.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (QR.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := andContra n (PR.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (QR.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

/- ===================== Or ===================== -/
def orCov {P P' Q Q' : Prop} :
    (m : MapClass) →
    Param (mapPropVariance m).1 (mapPropVariance m).2 P P' →
    Param (mapPropVariance m).1 (mapPropVariance m).2 Q Q' →
    MapHas m (fun (_ : P ∨ Q) (_ : P' ∨ Q') => PLift True)
  | map0,  _,  _  => {}
  | map1,  PR, QR => propMapHas (fun h => h.elim (fun p => .inl (PR.cov.map p)) (fun q => .inr (QR.cov.map q))) map1
  | map2a, PR, QR => propMapHas (fun h => h.elim (fun p => .inl (PR.cov.map p)) (fun q => .inr (QR.cov.map q))) map2a
  | map2b, PR, QR => propMapHas (fun h => h.elim (fun p => .inl (PR.cov.map p)) (fun q => .inr (QR.cov.map q))) map2b
  | map3,  PR, QR => propMapHas (fun h => h.elim (fun p => .inl (PR.cov.map p)) (fun q => .inr (QR.cov.map q))) map3
  | map4,  PR, QR => propMapHas (fun h => h.elim (fun p => .inl (PR.cov.map p)) (fun q => .inr (QR.cov.map q))) map4

def orContra {P P' Q Q' : Prop} :
    (n : MapClass) →
    Param (mapPropVariance n).2 (mapPropVariance n).1 P P' →
    Param (mapPropVariance n).2 (mapPropVariance n).1 Q Q' →
    MapHas n (fun (_ : P' ∨ Q') (_ : P ∨ Q) => PLift True)
  | map0,  _,  _  => {}
  | map1,  PR, QR => propMapHas (fun h => h.elim (fun p => .inl (PR.contra.map p)) (fun q => .inr (QR.contra.map q))) map1
  | map2a, PR, QR => propMapHas (fun h => h.elim (fun p => .inl (PR.contra.map p)) (fun q => .inr (QR.contra.map q))) map2a
  | map2b, PR, QR => propMapHas (fun h => h.elim (fun p => .inl (PR.contra.map p)) (fun q => .inr (QR.contra.map q))) map2b
  | map3,  PR, QR => propMapHas (fun h => h.elim (fun p => .inl (PR.contra.map p)) (fun q => .inr (QR.contra.map q))) map3
  | map4,  PR, QR => propMapHas (fun h => h.elim (fun p => .inl (PR.contra.map p)) (fun q => .inr (QR.contra.map q))) map4

@[trocq] def paramOrR (m n : MapClass) (P P' : Prop)
    (PR : Param (propVariance (m, n)).1 (propVariance (m, n)).2 P P')
    (Q Q' : Prop) (QR : Param (propVariance (m, n)).1 (propVariance (m, n)).2 Q Q') :
    Param m n (P ∨ Q) (P' ∨ Q') where
  R := fun _ _ => PLift True
  cov := orCov m (PR.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (QR.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := orContra n (PR.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (QR.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

/- ===================== Not (contravariant) ===================== -/
def notCov {P P' : Prop} :
    (m : MapClass) → Param (mapPropVariance m).2 (mapPropVariance m).1 P P' →
    MapHas m (fun (_ : ¬ P) (_ : ¬ P') => PLift True)
  | map0,  _  => {}
  | map1,  PR => propMapHas (fun h p' => h (PR.contra.map p')) map1
  | map2a, PR => propMapHas (fun h p' => h (PR.contra.map p')) map2a
  | map2b, PR => propMapHas (fun h p' => h (PR.contra.map p')) map2b
  | map3,  PR => propMapHas (fun h p' => h (PR.contra.map p')) map3
  | map4,  PR => propMapHas (fun h p' => h (PR.contra.map p')) map4

def notContra {P P' : Prop} :
    (n : MapClass) → Param (mapPropVariance n).1 (mapPropVariance n).2 P P' →
    MapHas n (fun (_ : ¬ P') (_ : ¬ P) => PLift True)
  | map0,  _  => {}
  | map1,  PR => propMapHas (fun h p => h (PR.cov.map p)) map1
  | map2a, PR => propMapHas (fun h p => h (PR.cov.map p)) map2a
  | map2b, PR => propMapHas (fun h p => h (PR.cov.map p)) map2b
  | map3,  PR => propMapHas (fun h p => h (PR.cov.map p)) map3
  | map4,  PR => propMapHas (fun h p => h (PR.cov.map p)) map4

@[trocq] def paramNotR (m n : MapClass) (P P' : Prop)
    (PR : Param (notVariance (m, n)).1 (notVariance (m, n)).2 P P') :
    Param m n (¬ P) (¬ P') where
  R := fun _ _ => PLift True
  cov := notCov m (PR.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := notContra n (PR.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

/- ===================== Iff (both directions of each part) ===================== -/
def iffCov {P P' Q Q' : Prop} :
    (m : MapClass) →
    Param (mapIffVariance m).1 (mapIffVariance m).2 P P' →
    Param (mapIffVariance m).1 (mapIffVariance m).2 Q Q' →
    MapHas m (fun (_ : P ↔ Q) (_ : P' ↔ Q') => PLift True)
  | map0,  _,  _  => {}
  | map1,  PR, QR => propMapHas (fun h => ⟨fun p' => QR.cov.map (h.mp (PR.contra.map p')), fun q' => PR.cov.map (h.mpr (QR.contra.map q'))⟩) map1
  | map2a, PR, QR => propMapHas (fun h => ⟨fun p' => QR.cov.map (h.mp (PR.contra.map p')), fun q' => PR.cov.map (h.mpr (QR.contra.map q'))⟩) map2a
  | map2b, PR, QR => propMapHas (fun h => ⟨fun p' => QR.cov.map (h.mp (PR.contra.map p')), fun q' => PR.cov.map (h.mpr (QR.contra.map q'))⟩) map2b
  | map3,  PR, QR => propMapHas (fun h => ⟨fun p' => QR.cov.map (h.mp (PR.contra.map p')), fun q' => PR.cov.map (h.mpr (QR.contra.map q'))⟩) map3
  | map4,  PR, QR => propMapHas (fun h => ⟨fun p' => QR.cov.map (h.mp (PR.contra.map p')), fun q' => PR.cov.map (h.mpr (QR.contra.map q'))⟩) map4

def iffContra {P P' Q Q' : Prop} :
    (n : MapClass) →
    Param (mapIffVariance n).1 (mapIffVariance n).2 P P' →
    Param (mapIffVariance n).1 (mapIffVariance n).2 Q Q' →
    MapHas n (fun (_ : P' ↔ Q') (_ : P ↔ Q) => PLift True)
  | map0,  _,  _  => {}
  | map1,  PR, QR => propMapHas (fun h => ⟨fun p => QR.contra.map (h.mp (PR.cov.map p)), fun q => PR.contra.map (h.mpr (QR.cov.map q))⟩) map1
  | map2a, PR, QR => propMapHas (fun h => ⟨fun p => QR.contra.map (h.mp (PR.cov.map p)), fun q => PR.contra.map (h.mpr (QR.cov.map q))⟩) map2a
  | map2b, PR, QR => propMapHas (fun h => ⟨fun p => QR.contra.map (h.mp (PR.cov.map p)), fun q => PR.contra.map (h.mpr (QR.cov.map q))⟩) map2b
  | map3,  PR, QR => propMapHas (fun h => ⟨fun p => QR.contra.map (h.mp (PR.cov.map p)), fun q => PR.contra.map (h.mpr (QR.cov.map q))⟩) map3
  | map4,  PR, QR => propMapHas (fun h => ⟨fun p => QR.contra.map (h.mp (PR.cov.map p)), fun q => PR.contra.map (h.mpr (QR.cov.map q))⟩) map4

@[trocq] def paramIffR (m n : MapClass) (P P' : Prop)
    (PR : Param (iffVariance (m, n)).1 (iffVariance (m, n)).2 P P')
    (Q Q' : Prop) (QR : Param (iffVariance (m, n)).1 (iffVariance (m, n)).2 Q Q') :
    Param m n (P ↔ Q) (P' ↔ Q') where
  R := fun _ _ => PLift True
  cov := iffCov m (PR.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (QR.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := iffContra n (PR.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (QR.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

end LeTrocq.ParamLib
