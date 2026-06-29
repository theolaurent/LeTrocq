/-
Classifying `@[trocq]`-tagged witnesses by their type.

A tagged constant `w` is one of four kinds, read off the conclusion of its (telescoped) type:
  • BASE       `w : Param m n A B`      (A,B closed consts, no binders)  — an equivalence of types.
  • RELATOR    `w : ∀ …, Param m n (P …) (P' …)`                        — relates an applied head `P`.
  • TYPEFORMER `w : ∀ params, F args → F' args' → Sort`  (concl a SORT) — the parametricity RELATION of a
                parameterized type `F` (e.g. `List`/`Option`); the native translation uses it to cross
                `F a`. Its constructors/recursor register separately as ordinary TERM primitives.
  • TERM       `w : ∀ …, R … (c …) (c' …)`  (R a bare relation)        — relates a term head `c ↦ c'`.

The per-surface builders (`Solver.buildAtoms`/`buildConsts`, `Translate.buildCtx`) consume these. The
`@[trocq]` attribute (`Attr.lean`) runs `parseEntry` eagerly and stores the resulting `RegKind`.
-/
import Trocq.Core
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

/-- the classification of a `@[trocq]` witness. The witness itself is kept as its NAME (`witName`), not a
    baked `mkConst`: consumers re-create it with fresh universe levels (`mkConstWithFreshMVarLevels`), so
    universe-polymorphic witnesses register and instantiate correctly. -/
inductive RegKind
  | base       (headA headB : Name) (tyA tyB : Expr) (witName : Name) (cls : ParamClass)
  | relator    (headA : Name) (witName : Name) (cls : ParamClass)
  | typeFormer (headA headB : Name) (relName : Name)
  | propPrim   (headA headB : Name) (witName : Name)
  | term       (headA : Name) (bTerm : Expr) (witName : Name)
  deriving Inhabited

/-- classify a tagged constant `w` from its type (see the kinds above). The const is built with its own
    level params (`mkConstWithLevelParams`) so a universe-polymorphic `w` telescopes without a level error. -/
def parseEntry (w : Name) : MetaM RegKind := do
  let wit ← mkConstWithLevelParams w
  forallTelescopeReducing (← inferType wit) fun bs concl => do
    let args := concl.getAppArgs
    if concl.isSort then
      -- a RELATION FORMER `F-args → F'-args' → Sort`: the parametricity relation of a parameterized type.
      -- The telescope eats the two related objects too, so they are the last two binders; their head
      -- constants name the A-/B-side type formers (equal for a homogeneous type like `List`/`Option`).
      unless bs.size ≥ 2 do throwError "trocq: type former {w} must relate two objects"
      let some hA := (← inferType bs[bs.size - 2]!).getAppFn.constName?
        | throwError "trocq: type former {w} A-object has no head constant"
      let some hB := (← inferType bs[bs.size - 1]!).getAppFn.constName?
        | throwError "trocq: type former {w} B-object has no head constant"
      return .typeFormer hA hB w
    else if concl.getAppFn.isConstOf ``Param then
      let cls := (← exprToMapClass args[0]!, ← exprToMapClass args[1]!)
      let A := args[2]!; let B := args[3]!
      if bs.isEmpty && A.isConst && B.isConst then
        return .base A.constName! B.constName! A B w cls
      else
        let some hA := A.getAppFn.constName? | throwError "trocq: relator {w} has no head constant"
        return .relator hA w cls
    else if concl.getAppFn.isConstOf ``PLift && args.size == 1 && args[0]!.getAppFn.isConstOf ``Iff then
      -- a PROP primitive `pR : ∀ …, PLift (p … ↔ p' …)` relating two predicates `p ↦ p'` by equivalence.
      let iff := args[0]!.getAppArgs
      let some hA := iff[0]!.getAppFn.constName? | throwError "trocq: prop primitive {w} has no A-side head"
      let some hB := iff[1]!.getAppFn.constName? | throwError "trocq: prop primitive {w} has no B-side head"
      return .propPrim hA hB w
    else
      if args.size ≥ 2 then
        let some hA := args[args.size - 2]!.getAppFn.constName?
          | throwError "trocq: term primitive {w} has no A-side head constant"
        return .term hA args[args.size - 1]!.getAppFn w
      else throwError "trocq: cannot classify {w} : {← inferType wit}"

end Trocq
