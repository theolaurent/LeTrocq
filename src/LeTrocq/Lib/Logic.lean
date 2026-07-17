/-
The logical connectives (`Not`, `And`, `Or`, `Iff`) — standard-library registration. Each is a graded relator
`⋆ P Q ≃ ⋆ P' Q'` built at the demanded class `(m,n)`. A proposition carries no data above class 1
(completeness/coherence free by proof irrelevance, `propMap`), so a `Prop` PART is only ever demanded up to
`meet · map1`. `And`/`Or` are covariant in both parts; `Not` is CONTRAVARIANT (variance negated); `Iff` uses
both directions of each part, so its part is `(1,1)` whenever either output class is ≥ 1. The carried relation
is the trivial `fun _ _ => PLift True`.
-/
import LeTrocq.Driver.Registry
import LeTrocq.Combinators.Universe
namespace LeTrocq.Lib
open LeTrocq MapClass

/- ===================== variance tables (a `Prop` part is capped at `meet · map1`) ===================== -/
/-- covariant part variance (`And`/`Or`): a part is needed up to class 1, free above. -/
def mapPropVariance : MapClass → ParamClass
  | map0 => (map0, map0)
  | _    => (map1, map0)

def propVariance (c : ParamClass) : ParamClass := ParamClass.variance mapPropVariance c

/-- `Not` is contravariant: it needs the part in the mirror direction. -/
def notVariance (c : ParamClass) : ParamClass := propVariance (c.2, c.1)

/-- `Iff` uses both directions of each part in each direction of the whole, so the part is `(1,1)` unless
    the output is `(0,0)`. -/
def mapIffVariance : MapClass → ParamClass
  | map0 => (map0, map0)
  | _    => (map1, map1)

def iffVariance (c : ParamClass) : ParamClass := ParamClass.variance mapIffVariance c

/- ===================== And ===================== -/
def andCov {P P' Q Q' : Prop} :
    (m : MapClass) →
    Param (mapPropVariance m).1 (mapPropVariance m).2 P P' →
    Param (mapPropVariance m).1 (mapPropVariance m).2 Q Q' →
    Map m (fun (_ : P ∧ Q) (_ : P' ∧ Q') => PLift True)
  | map0,  _,  _  => {}
  | map1,  pW, qW => propMap (fun h => ⟨pW.cov.map h.1, qW.cov.map h.2⟩) map1
  | map2a, pW, qW => propMap (fun h => ⟨pW.cov.map h.1, qW.cov.map h.2⟩) map2a
  | map2b, pW, qW => propMap (fun h => ⟨pW.cov.map h.1, qW.cov.map h.2⟩) map2b
  | map3,  pW, qW => propMap (fun h => ⟨pW.cov.map h.1, qW.cov.map h.2⟩) map3
  | map4,  pW, qW => propMap (fun h => ⟨pW.cov.map h.1, qW.cov.map h.2⟩) map4

def andContra {P P' Q Q' : Prop} :
    (n : MapClass) →
    Param (mapPropVariance n).2 (mapPropVariance n).1 P P' →
    Param (mapPropVariance n).2 (mapPropVariance n).1 Q Q' →
    Map n (fun (_ : P' ∧ Q') (_ : P ∧ Q) => PLift True)
  | map0,  _,  _  => {}
  | map1,  pW, qW => propMap (fun h => ⟨pW.contra.map h.1, qW.contra.map h.2⟩) map1
  | map2a, pW, qW => propMap (fun h => ⟨pW.contra.map h.1, qW.contra.map h.2⟩) map2a
  | map2b, pW, qW => propMap (fun h => ⟨pW.contra.map h.1, qW.contra.map h.2⟩) map2b
  | map3,  pW, qW => propMap (fun h => ⟨pW.contra.map h.1, qW.contra.map h.2⟩) map3
  | map4,  pW, qW => propMap (fun h => ⟨pW.contra.map h.1, qW.contra.map h.2⟩) map4

@[trocq] def paramAnd (m n : MapClass) (P P' : Prop)
    (pW : Param (propVariance (m, n)).1 (propVariance (m, n)).2 P P')
    (Q Q' : Prop) (qW : Param (propVariance (m, n)).1 (propVariance (m, n)).2 Q Q') :
    Param m n (P ∧ Q) (P' ∧ Q') where
  R := fun _ _ => PLift True
  cov := andCov m (pW.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (qW.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := andContra n (pW.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (qW.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

/- ===================== Or ===================== -/
def orCov {P P' Q Q' : Prop} :
    (m : MapClass) →
    Param (mapPropVariance m).1 (mapPropVariance m).2 P P' →
    Param (mapPropVariance m).1 (mapPropVariance m).2 Q Q' →
    Map m (fun (_ : P ∨ Q) (_ : P' ∨ Q') => PLift True)
  | map0,  _,  _  => {}
  | map1,  pW, qW => propMap (fun h => h.elim (fun p => .inl (pW.cov.map p)) (fun q => .inr (qW.cov.map q))) map1
  | map2a, pW, qW => propMap (fun h => h.elim (fun p => .inl (pW.cov.map p)) (fun q => .inr (qW.cov.map q))) map2a
  | map2b, pW, qW => propMap (fun h => h.elim (fun p => .inl (pW.cov.map p)) (fun q => .inr (qW.cov.map q))) map2b
  | map3,  pW, qW => propMap (fun h => h.elim (fun p => .inl (pW.cov.map p)) (fun q => .inr (qW.cov.map q))) map3
  | map4,  pW, qW => propMap (fun h => h.elim (fun p => .inl (pW.cov.map p)) (fun q => .inr (qW.cov.map q))) map4

def orContra {P P' Q Q' : Prop} :
    (n : MapClass) →
    Param (mapPropVariance n).2 (mapPropVariance n).1 P P' →
    Param (mapPropVariance n).2 (mapPropVariance n).1 Q Q' →
    Map n (fun (_ : P' ∨ Q') (_ : P ∨ Q) => PLift True)
  | map0,  _,  _  => {}
  | map1,  pW, qW => propMap (fun h => h.elim (fun p => .inl (pW.contra.map p)) (fun q => .inr (qW.contra.map q))) map1
  | map2a, pW, qW => propMap (fun h => h.elim (fun p => .inl (pW.contra.map p)) (fun q => .inr (qW.contra.map q))) map2a
  | map2b, pW, qW => propMap (fun h => h.elim (fun p => .inl (pW.contra.map p)) (fun q => .inr (qW.contra.map q))) map2b
  | map3,  pW, qW => propMap (fun h => h.elim (fun p => .inl (pW.contra.map p)) (fun q => .inr (qW.contra.map q))) map3
  | map4,  pW, qW => propMap (fun h => h.elim (fun p => .inl (pW.contra.map p)) (fun q => .inr (qW.contra.map q))) map4

@[trocq] def paramOr (m n : MapClass) (P P' : Prop)
    (pW : Param (propVariance (m, n)).1 (propVariance (m, n)).2 P P')
    (Q Q' : Prop) (qW : Param (propVariance (m, n)).1 (propVariance (m, n)).2 Q Q') :
    Param m n (P ∨ Q) (P' ∨ Q') where
  R := fun _ _ => PLift True
  cov := orCov m (pW.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (qW.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := orContra n (pW.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (qW.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

/- ===================== Not (contravariant) ===================== -/
def notCov {P P' : Prop} :
    (m : MapClass) → Param (mapPropVariance m).2 (mapPropVariance m).1 P P' →
    Map m (fun (_ : ¬ P) (_ : ¬ P') => PLift True)
  | map0,  _  => {}
  | map1,  pW => propMap (fun h p' => h (pW.contra.map p')) map1
  | map2a, pW => propMap (fun h p' => h (pW.contra.map p')) map2a
  | map2b, pW => propMap (fun h p' => h (pW.contra.map p')) map2b
  | map3,  pW => propMap (fun h p' => h (pW.contra.map p')) map3
  | map4,  pW => propMap (fun h p' => h (pW.contra.map p')) map4

def notContra {P P' : Prop} :
    (n : MapClass) → Param (mapPropVariance n).1 (mapPropVariance n).2 P P' →
    Map n (fun (_ : ¬ P') (_ : ¬ P) => PLift True)
  | map0,  _  => {}
  | map1,  pW => propMap (fun h p => h (pW.cov.map p)) map1
  | map2a, pW => propMap (fun h p => h (pW.cov.map p)) map2a
  | map2b, pW => propMap (fun h p => h (pW.cov.map p)) map2b
  | map3,  pW => propMap (fun h p => h (pW.cov.map p)) map3
  | map4,  pW => propMap (fun h p => h (pW.cov.map p)) map4

@[trocq] def paramNot (m n : MapClass) (P P' : Prop)
    (pW : Param (notVariance (m, n)).1 (notVariance (m, n)).2 P P') :
    Param m n (¬ P) (¬ P') where
  R := fun _ _ => PLift True
  cov := notCov m (pW.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := notContra n (pW.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

/- ===================== Iff (both directions of each part) ===================== -/
def iffCov {P P' Q Q' : Prop} :
    (m : MapClass) →
    Param (mapIffVariance m).1 (mapIffVariance m).2 P P' →
    Param (mapIffVariance m).1 (mapIffVariance m).2 Q Q' →
    Map m (fun (_ : P ↔ Q) (_ : P' ↔ Q') => PLift True)
  | map0,  _,  _  => {}
  | map1,  pW, qW => propMap (fun h => ⟨fun p' => qW.cov.map (h.mp (pW.contra.map p')), fun q' => pW.cov.map (h.mpr (qW.contra.map q'))⟩) map1
  | map2a, pW, qW => propMap (fun h => ⟨fun p' => qW.cov.map (h.mp (pW.contra.map p')), fun q' => pW.cov.map (h.mpr (qW.contra.map q'))⟩) map2a
  | map2b, pW, qW => propMap (fun h => ⟨fun p' => qW.cov.map (h.mp (pW.contra.map p')), fun q' => pW.cov.map (h.mpr (qW.contra.map q'))⟩) map2b
  | map3,  pW, qW => propMap (fun h => ⟨fun p' => qW.cov.map (h.mp (pW.contra.map p')), fun q' => pW.cov.map (h.mpr (qW.contra.map q'))⟩) map3
  | map4,  pW, qW => propMap (fun h => ⟨fun p' => qW.cov.map (h.mp (pW.contra.map p')), fun q' => pW.cov.map (h.mpr (qW.contra.map q'))⟩) map4

def iffContra {P P' Q Q' : Prop} :
    (n : MapClass) →
    Param (mapIffVariance n).1 (mapIffVariance n).2 P P' →
    Param (mapIffVariance n).1 (mapIffVariance n).2 Q Q' →
    Map n (fun (_ : P' ↔ Q') (_ : P ↔ Q) => PLift True)
  | map0,  _,  _  => {}
  | map1,  pW, qW => propMap (fun h => ⟨fun p => qW.contra.map (h.mp (pW.cov.map p)), fun q => pW.contra.map (h.mpr (qW.cov.map q))⟩) map1
  | map2a, pW, qW => propMap (fun h => ⟨fun p => qW.contra.map (h.mp (pW.cov.map p)), fun q => pW.contra.map (h.mpr (qW.cov.map q))⟩) map2a
  | map2b, pW, qW => propMap (fun h => ⟨fun p => qW.contra.map (h.mp (pW.cov.map p)), fun q => pW.contra.map (h.mpr (qW.cov.map q))⟩) map2b
  | map3,  pW, qW => propMap (fun h => ⟨fun p => qW.contra.map (h.mp (pW.cov.map p)), fun q => pW.contra.map (h.mpr (qW.cov.map q))⟩) map3
  | map4,  pW, qW => propMap (fun h => ⟨fun p => qW.contra.map (h.mp (pW.cov.map p)), fun q => pW.contra.map (h.mpr (qW.cov.map q))⟩) map4

@[trocq] def paramIff (m n : MapClass) (P P' : Prop)
    (pW : Param (iffVariance (m, n)).1 (iffVariance (m, n)).2 P P')
    (Q Q' : Prop) (qW : Param (iffVariance (m, n)).1 (iffVariance (m, n)).2 Q Q') :
    Param m n (P ↔ Q) (P' ↔ Q') where
  R := fun _ _ => PLift True
  cov := iffCov m (pW.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (qW.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
  contra := iffContra n (pW.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))
    (qW.weaken (by cases m <;> cases n <;> rfl) (by cases m <;> cases n <;> rfl))

end LeTrocq.Lib
