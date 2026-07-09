/- The driver end to end: Expr → demand-driven `assemble` → witness. `assemble` walks the type once, pushing a
   demanded class top-down and building each node's `Param` at the minimal class demanded (no constraint graph,
   no fixpoint). -/
import Lean
import LeTrocq
import Examples.NatUnary
import Examples.WTree
open Lean Lean.Meta Lean.Elab Lean.Elab.Command

namespace LeTrocq.Tests
open LeTrocq LeTrocq.Driver.Transfer MapClass LeTrocq.Examples

def flagshipTy := ∀ A : Type, A → A

/- witness for `Nat → Nat` at root (1,0): built by the graded `paramArrow` at each node's minimal class
   (`arrowVariance (1,0)` ⇒ domain at (0,1), codomain at (1,0)) — no build-(3,3)-then-weaken. -/
run_cmd Command.liftTermElabM do
  let e ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let wit ← transferType e (← counterpart e) (map1, map0)
  let ty ← instantiateMVars (← inferType wit)
  addDecl (.defnDecl { name := `LeTrocq.Tests.transferred, levelParams := [], type := ty, value := wit,
                       hints := .opaque, safety := .safe })

/- a nested arrow `Nat → Nat → Nat` at (1,0): multi-level assembly, each node at its own class. -/
run_cmd Command.liftTermElabM do
  let e ← mkArrow (mkConst ``Nat) (← mkArrow (mkConst ``Nat) (mkConst ``Nat))
  let wit ← transferType e (← counterpart e) (map1, map0)
  let ty ← instantiateMVars (← inferType wit)
  addDecl (.defnDecl { name := `LeTrocq.Tests.transferred2, levelParams := [], type := ty, value := wit,
                       hints := .opaque, safety := .safe })

/- the witness is a real `Param (1,0) (Nat→Nat) (Unary→Unary)`, forward map = native function transport, and
   it COMPUTES: -/
example : LeTrocq.Tests.transferred.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl
/-- info: 'LeTrocq.Tests.transferred' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms LeTrocq.Tests.transferred

/- the nested witness is a real `Param (1,0) (Nat→Nat→Nat) (Unary→Unary→Unary)` and computes: -/
example : LeTrocq.Tests.transferred2.cov.map (· + ·) Unary.z (Unary.s Unary.z) = Unary.s Unary.z := rfl
example : True := by
  have : Param .map1 .map0 (Nat → Nat → Nat) (Unary → Unary → Unary) := LeTrocq.Tests.transferred2
  trivial

/- FORALL + TYPE end-to-end: the polymorphic `∀ A : Type, A → A` at (0,1) — builds the universe domain
   (`paramTypeAt`), goes under the binder, and assembles the body `A → A` from the bound variable's witness.
   The paper's flagship, now assembled, not just inferred. -/
def flagshipTy2 := ∀ A : Type, A → A
run_cmd Command.liftTermElabM do
  let e := (← getConstInfo ``flagshipTy2).value!
  let wit ← transferType e (← counterpart e) (map0, map1)
  let ty ← instantiateMVars (← inferType wit)
  addDecl (.defnDecl { name := `LeTrocq.Tests.flagshipWit, levelParams := [], type := ty, value := wit,
                       hints := .opaque, safety := .safe })

/- the witness relates the polymorphic type to itself at (0,1) (asserted via a proof term, since it is
   noncomputable — uses funext): -/
example : True := by
  have : Param .map0 .map1 (∀ A : Type, A → A) (∀ A : Type, A → A) := LeTrocq.Tests.flagshipWit
  trivial
/-- info: 'LeTrocq.Tests.flagshipWit' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms LeTrocq.Tests.flagshipWit

/- MAP_TYPE: the same type at (2b,0). The universe's outer class is `forallVariance (2b,0).1 = (0,2a)` (≤ the
   (2a,2a) ceiling, so no univalence needed); the bound `A` is offered at inner class (4,4), the pinned top,
   independent of the capped outer. -/
run_cmd Command.liftTermElabM do
  let e := (← getConstInfo ``flagshipTy2).value!
  let wit ← transferType e (← counterpart e) (map2b, map0)
  let ty ← instantiateMVars (← inferType wit)
  addDecl (.defnDecl { name := `LeTrocq.Tests.flagshipWit2b, levelParams := [], type := ty, value := wit,
                       hints := .opaque, safety := .safe })
example : True := by
  have : Param .map2b .map0 (∀ A : Type, A → A) (∀ A : Type, A → A) := LeTrocq.Tests.flagshipWit2b
  trivial

/- UNIVERSE POLYMORPHISM: the universe combinator carries the actual level, so `∀ A : Type w, A → A` transfers
   at any `w` (not just `w = 0`). -/
def flagshipTy2Lvl2 := ∀ A : Type 2, A → A
run_cmd Command.liftTermElabM do
  let e := (← getConstInfo ``flagshipTy2Lvl2).value!
  let wit ← transferType e (← counterpart e) (map0, map1)
  addDecl (.defnDecl { name := `LeTrocq.Tests.flagshipWitLvl2, levelParams := [],
                       type := ← instantiateMVars (← inferType wit), value := ← instantiateMVars wit,
                       hints := .opaque, safety := .safe })
example : True := by
  have : Param .map0 .map1 (∀ A : Type 2, A → A) (∀ A : Type 2, A → A) := LeTrocq.Tests.flagshipWitLvl2
  trivial

/- a genuinely universe-polymorphic input (a level param `u`, not a literal): the level is preserved
   (`defaultFreeLevels` zeroes only mvars), so the witness is itself universe-polymorphic — instantiated here
   at level 5. -/
universe u
def flagshipTyU := ∀ A : Type u, A → A
run_cmd Command.liftTermElabM do
  let ci ← getConstInfo ``flagshipTyU
  let wit ← transferType ci.value! (← counterpart ci.value!) (map0, map1)
  addDecl (.defnDecl { name := `LeTrocq.Tests.flagshipWitU, levelParams := ci.levelParams,
                       type := ← instantiateMVars (← inferType wit), value := ← instantiateMVars wit,
                       hints := .opaque, safety := .safe })
example : True := by
  have : Param .map0 .map1 (∀ A : Type 5, A → A) (∀ A : Type 5, A → A) := LeTrocq.Tests.flagshipWitU.{5}
  trivial

/- (4,4) end-to-end: `Nat → Nat` at the top class — the arrow propagates the full equivalence (the `(4,4)`
   coherence `rInMapK` holds by subsingleton). -/
run_cmd Command.liftTermElabM do
  let e ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let wit ← transferType e (← counterpart e) (map4, map4)
  let ty ← instantiateMVars (← inferType wit)
  addDecl (.defnDecl { name := `LeTrocq.Tests.transferred44, levelParams := [], type := ty, value := wit,
                       hints := .opaque, safety := .safe })
example : LeTrocq.Tests.transferred44.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl
example : True := by
  have : Param .map4 .map4 (Nat → Nat) (Unary → Unary) := LeTrocq.Tests.transferred44
  trivial

/- `Nat → Nat` at several intermediate classes — each witness computes. -/
run_cmd Command.liftTermElabM do
  let e ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let w3 ← transferType e (← counterpart e) (map3, map3)
  addDecl (.defnDecl { name := `LeTrocq.Tests.tr33, levelParams := [],
                       type := ← instantiateMVars (← inferType w3), value := ← instantiateMVars w3,
                       hints := .opaque, safety := .safe })
  let w2a ← transferType e (← counterpart e) (map2a, map0)
  addDecl (.defnDecl { name := `LeTrocq.Tests.tr2a, levelParams := [],
                       type := ← instantiateMVars (← inferType w2a), value := ← instantiateMVars w2a,
                       hints := .opaque, safety := .safe })
example : LeTrocq.Tests.tr33.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl
example : LeTrocq.Tests.tr2a.cov.map Nat.succ Unary.z = Unary.s Unary.z := rfl

/- a higher-order domain `(Nat → Nat) → Nat` at (1,0): assembly nests through the arrow domain. -/
run_cmd Command.liftTermElabM do
  let e ← mkArrow (← mkArrow (mkConst ``Nat) (mkConst ``Nat)) (mkConst ``Nat)
  let wit ← transferType e (← counterpart e) (map1, map0)
  addDecl (.defnDecl { name := `LeTrocq.Tests.trHO, levelParams := [],
                       type := ← instantiateMVars (← inferType wit), value := ← instantiateMVars wit,
                       hints := .opaque, safety := .safe })
example : True := by
  have : Param .map1 .map0 ((Nat → Nat) → Nat) ((Unary → Unary) → Unary) := LeTrocq.Tests.trHO
  trivial

/- ===================== VARIANCE for parameterized types (graded `paramList`) =====================
   `List` crosses through a graded relator whose element class tracks the demanded output class
   (`listVariance`), not a fixed-(4,4) relator weakened at the end.
   MINIMALITY: `List Nat` at demand (1,0) builds its element at (1,0), not (4,4), and still computes. -/
run_cmd Command.liftTermElabM do
  let e := mkApp (mkConst ``List) (mkConst ``Nat)
  let wit ← transferType e (← counterpart e) (map1, map0)
  addDecl (.defnDecl { name := `LeTrocq.Tests.listNatLow, levelParams := [],
                       type := ← instantiateMVars (← inferType wit), value := ← instantiateMVars wit,
                       hints := .opaque, safety := .safe })
example : LeTrocq.Tests.listNatLow.cov.map [Nat.zero, Nat.succ Nat.zero] = [Unary.z, Unary.s Unary.z] := rfl

/- EXPRESSIVENESS: a PARTIAL base (a one-way (1,0) map, not an equivalence) composes under `List`. The graded
   relator needs the element only at (1,0); under the former fixed-(4,4) relator this was unreachable and
   `List Src` did not transfer. -/
inductive Src | a | b
inductive Tgt | x | y
def SrcTgtR : Src → Tgt → Type := fun _ _ => PLift True
@[trocq] def paramSrcTgt : Param map1 map0 Src Tgt where
  R := SrcTgtR
  cov := { map := fun _ => Tgt.x }
  contra := {}

run_cmd Command.liftTermElabM do
  let e := mkApp (mkConst ``List) (mkConst ``Src)
  let wit ← transferType e (← counterpart e) (map1, map0)
  addDecl (.defnDecl { name := `LeTrocq.Tests.listSrcWit, levelParams := [],
                       type := ← instantiateMVars (← inferType wit), value := ← instantiateMVars wit,
                       hints := .opaque, safety := .safe })
example : True := by
  have : Param .map1 .map0 (List Src) (List Tgt) := LeTrocq.Tests.listSrcWit
  trivial
example : LeTrocq.Tests.listSrcWit.cov.map [Src.a, Src.b] = [Tgt.x, Tgt.x] := rfl
/-- info: 'LeTrocq.Tests.listSrcWit' does not depend on any axioms -/
#guard_msgs in #print axioms LeTrocq.Tests.listSrcWit

/- THE COVARIANT BATCH — `Option`, `Prod`, `Sum`, `Array` are graded like `List`, so each composes the same
   partial (1,0) base at demand (1,0) and computes. (Ungraded, the element would be forced to (4,4) and all
   four would fail.) -/
run_cmd Command.liftTermElabM do
  let mk (nm : Name) (e : Expr) : TermElabM Unit := do
    let wit ← transferType e (← counterpart e) (map1, map0)
    addDecl (.defnDecl { name := nm, levelParams := [],
                         type := ← instantiateMVars (← inferType wit), value := ← instantiateMVars wit,
                         hints := .opaque, safety := .safe })
  mk `LeTrocq.Tests.optionSrcWit (mkApp (mkConst ``Option) (mkConst ``Src))
  mk `LeTrocq.Tests.prodSrcWit   (mkApp2 (mkConst ``Prod) (mkConst ``Src) (mkConst ``Src))
  mk `LeTrocq.Tests.sumSrcWit    (mkApp2 (mkConst ``Sum) (mkConst ``Src) (mkConst ``Src))
  mk `LeTrocq.Tests.arraySrcWit  (mkApp (mkConst ``Array) (mkConst ``Src))

example : LeTrocq.Tests.optionSrcWit.cov.map (some Src.a) = some Tgt.x := rfl
example : LeTrocq.Tests.prodSrcWit.cov.map (Src.a, Src.b) = (Tgt.x, Tgt.x) := rfl
example : LeTrocq.Tests.sumSrcWit.cov.map (Sum.inl Src.a) = (Sum.inl Tgt.x : Tgt ⊕ Tgt) := rfl
example : LeTrocq.Tests.arraySrcWit.cov.map #[Src.a, Src.b] = #[Tgt.x, Tgt.x] := rfl
/-- info: 'LeTrocq.Tests.prodSrcWit' does not depend on any axioms -/
#guard_msgs in #print axioms LeTrocq.Tests.prodSrcWit

/- THE DEPENDENT TYPES — `Sigma` and `Quot` are graded too (domain has the forall-style wrinkle: `Sigma`'s
   domain built at 2a, `Quot`'s coherence free). MINIMALITY: each transfers at (1,0) with the domain below
   (4,4), and the dependent forward map computes. -/
def sigNatNat : Type := Σ _ : Nat, Nat
def quotNatT  : Type := Quot (fun _ _ : Nat => True)
run_cmd Command.liftTermElabM do
  let mk (nm : Name) (tyNm : Name) : TermElabM Unit := do
    let e := (← getConstInfo tyNm).value!
    let wit ← transferType e (← counterpart e) (map1, map0)
    addDecl (.defnDecl { name := nm, levelParams := [],
                         type := ← instantiateMVars (← inferType wit), value := ← instantiateMVars wit,
                         hints := .opaque, safety := .safe })
  mk `LeTrocq.Tests.sigmaNatLow ``sigNatNat
  mk `LeTrocq.Tests.quotNatLow  ``quotNatT

example : LeTrocq.Tests.sigmaNatLow.cov.map ⟨Nat.zero, Nat.succ Nat.zero⟩ = ⟨Unary.z, Unary.s Unary.z⟩ := rfl
example : LeTrocq.Tests.quotNatLow.cov.map (Quot.mk _ (Nat.succ Nat.zero))
    = Quot.mk (fun _ _ : Unary => True) (Unary.s Unary.z) := rfl
/-- info: 'LeTrocq.Tests.sigmaNatLow' does not depend on any axioms -/
#guard_msgs in #print axioms LeTrocq.Tests.sigmaNatLow

/- `WTree` — the contravariant-family dependent type — is graded too: at demand (1,0) the domain and
   (contravariant) family each build at their `wtreeVariance` class. -/
def wtreeNatT : Type := WTree Nat (fun _ => Nat)
run_cmd Command.liftTermElabM do
  let e := (← getConstInfo ``wtreeNatT).value!
  let wit ← transferType e (← counterpart e) (map1, map0)
  addDecl (.defnDecl { name := `LeTrocq.Tests.wtreeNatLow, levelParams := [],
                       type := ← instantiateMVars (← inferType wit), value := ← instantiateMVars wit,
                       hints := .opaque, safety := .safe })
example : True := by
  have : Param .map1 .map0 (WTree Nat (fun _ => Nat)) (WTree Unary (fun _ => Unary)) :=
    LeTrocq.Tests.wtreeNatLow
  trivial
/-- info: 'LeTrocq.Tests.wtreeNatLow' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms LeTrocq.Tests.wtreeNatLow

/- a DIAGONAL term primitive (`Nat.zero ↦ Nat.zero`) is rejected at the `@[trocq]` tag site: a closed term
   transfers to itself automatically, so the registration is redundant. `parseEntry` catches it via `isDefEq`
   on the two related sides. -/
def diagRel : (fun (_ : Nat) (_ : Nat) => PLift True) Nat.zero Nat.zero := PLift.up trivial
/-- error: trocq: refusing diagonal term primitive LeTrocq.Tests.diagWit — it relates Nat.zero to itself; a closed term transfers to itself automatically, so a diagonal registration is redundant -/
#guard_msgs in @[trocq] def diagWit := diagRel

end LeTrocq.Tests
