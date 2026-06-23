/-
Classifying `@[trocq]`-tagged witnesses by their type.

A tagged constant `w` is one of three kinds, read off the conclusion of its (telescoped) type:
  • BASE     `w : Param m n A B`        (A,B closed consts, no binders)  — an equivalence of types.
  • RELATOR  `w : ∀ …, Param m n (P …) (P' …)`                          — relates an applied head `P`.
  • TERM     `w : ∀ …, R … (c …) (c' …)`  (R a bare relation, not Param) — relates a term head `c↦c'`.

The per-surface builders (`Solver.buildAtoms`/`buildConsts`, `Translate.buildCtx`) consume these.
-/
import Trocq.Combinators
import Trocq.Attr
import Lean
open Lean Lean.Meta
namespace Trocq

/-- read a `MapClass` constructor out of its `Expr`. -/
def exprToMapClass (e : Expr) : MetaM MapClass := do
  match e.getAppFn.constName? with
  | some ``MapClass.map0  => return .map0
  | some ``MapClass.map1  => return .map1
  | some ``MapClass.map2a => return .map2a
  | some ``MapClass.map2b => return .map2b
  | some ``MapClass.map3  => return .map3
  | some ``MapClass.map4  => return .map4
  | _ => throwError "trocq: cannot read a map class from {e}"

/-- the classification of a `@[trocq]` witness. -/
inductive RegKind
  | base    (headA headB : Name) (tyA tyB wit : Expr) (cls : ParamClass)
  | relator (headA : Name) (wit : Expr) (cls : ParamClass)
  | term    (headA : Name) (bTerm wit : Expr)

/-- classify a tagged constant `w` from its type (see the kinds above). -/
def parseEntry (w : Name) : MetaM RegKind := do
  let wit := mkConst w
  forallTelescopeReducing (← inferType wit) fun bs concl => do
    let args := concl.getAppArgs
    if concl.getAppFn.isConstOf ``Param then
      let cls := (← exprToMapClass args[0]!, ← exprToMapClass args[1]!)
      let A := args[2]!; let B := args[3]!
      if bs.isEmpty && A.isConst && B.isConst then
        return .base A.constName! B.constName! A B wit cls
      else
        let some hA := A.getAppFn.constName? | throwError "trocq: relator {w} has no head constant"
        return .relator hA wit cls
    else
      if args.size ≥ 2 then
        let some hA := args[args.size - 2]!.getAppFn.constName?
          | throwError "trocq: term primitive {w} has no A-side head constant"
        return .term hA args[args.size - 1]!.getAppFn wit
      else throwError "trocq: cannot classify {w} : {← inferType wit}"

end Trocq
