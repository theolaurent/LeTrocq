/-
THE `@[trocq]` REGISTRIES + relator argument-routing — the pure lookups the graded translation
(`LeTrocq.Transfer`) reads. This is NOT a grading solver anymore: grading is done inline by `Transfer.assemble`,
which pushes a demanded class top-down through the `depArrow`/`depPi`/`depType` tables (no constraint graph, no
fixpoint — see bidir_solver.md). What remains here is the registry side of the front↔back contract:

  • `buildAtoms`  — the type-atom registry from every `@[trocq]` BASE (both directions, via `Param.sym`).
  • `buildConsts` — the relator registry from every `@[trocq]` RELATOR (keyed by the applied head).
  • `relatorArgKinds` — read a relator's per-argument routing (`type` / `family` / `term`) off its type, so the
    abstraction-theorem `app` rule in `Transfer.assemble` knows how to consume each argument.
-/
import LeTrocq.Attr
import Lean
open Lean Lean.Meta
namespace LeTrocq.Solver
open LeTrocq MapClass

/- ===================== per-argument kind of a relator ===================== -/
/-- per-argument kind of a relator, read from its (telescoped) type grouped into abstraction-theorem
    triples `(a, a', aR)` by the SHAPE of the triple's relatedness `aR`:
      • `.type (m,n)`          — `aR : Param m n A A'`                  (a TYPE argument);
      • `.family (m,n) domIdx` — `aR : ∀ a a' (aR : RA a a'), Param m n (B a)(B' a')` (a dependent type
                                 FAMILY, e.g. `Sigma`/`WTree`'s `β`). `domIdx` is the index of the TYPE
                                 argument that is the family's domain `A` — read off `B`'s own binder type,
                                 so the family need NOT sit right after its domain;
      • `.term`                — `aR` a bare relation                  (a TERM argument). -/
inductive ArgKind
  | type   (cls : ParamClass)
  | family (cls : ParamClass) (domIdx : Nat)
  | term
  deriving Inhabited

/-- read a relator's per-argument routing off its type (see `ArgKind`). Consumed by `Transfer.assemble`'s
    abstraction-theorem `app` rule: it walks the relator's actual arguments and, per this routing, builds each
    one's `Param` (a TYPE arg / a FAMILY arg) or sends it to the term half (a TERM arg). -/
def relatorArgKinds (wit : Expr) : MetaM (Array ArgKind) := do
  forallTelescopeReducing (← inferType wit) fun bs _ => do
    let triples ← chunkTriples "relator" wit bs
    let mut kinds : Array ArgKind := #[]
    let mut lastTypeIdx : Nat := 0
    for j in [0 : triples.size] do
      let (aBinder, _, aR) := triples[j]!                 -- `(a, a', aR)`: the A-binder and the relatedness
      let relTy ← inferType aR
      if relTy.getAppFn.isConstOf ``Param then
        let a := relTy.getAppArgs
        kinds := kinds.push (.type (← exprToMapClass a[0]!, ← exprToMapClass a[1]!))
        lastTypeIdx := j
      else
        -- a FAMILY arg's relatedness telescopes to a `Param`; anything else is a bare-relation TERM arg.
        let fam? ← forallTelescopeReducing relTy fun _ concl => do
          if concl.getAppFn.isConstOf ``Param then
            let a := concl.getAppArgs
            return some (← exprToMapClass a[0]!, ← exprToMapClass a[1]!)
          else return none
        match fam? with
        | some cls =>
            -- the family binder `B : A → _` names its domain `A`; find the TYPE-arg triple whose A-binder
            -- IS that `A` (so the right witness is used even if the family is not adjacent to it).
            -- Fall back to the most recent type argument if `A` is not a bare earlier binder.
            let domA := (← whnf (← inferType aBinder)).bindingDomain!
            let mut domIdx := lastTypeIdx
            for k in [0 : j] do
              if triples[k]!.1 == domA then domIdx := k
            kinds := kinds.push (.family cls domIdx)
        | none => kinds := kinds.push .term
    return kinds

/- ===================== registries from the `@[trocq]` extension ===================== -/
/-- type-atom registry from every `@[trocq]` BASE, BOTH directions (the base and its `Param.sym`), so a
    type built over either side of an equivalence resolves by head match. -/
def buildAtoms : MetaM (NameMap (Expr × Expr × ParamClass)) := do
  let mut m := mkNameMap _
  for e in trocqEntries (← getEnv) do
    if let .base hA hB tyA tyB witName cls := e then
      let wit ← mkConstWithFreshMVarLevels witName
      m ← insertBidir m hA (some hB) (tyB, wit, cls)
        (return (tyA, ← mkAppM ``Param.sym #[wit], (cls.2, cls.1)))
  return m

/-- constant registry from every `@[trocq]` RELATOR (keyed by the applied head, as written). Includes the
    prelude `Quot` relator (`LeTrocq.ParamLib.paramQuotR`), which registers like any other — not a built-in. -/
def buildConsts : MetaM (NameMap (Expr × ParamClass)) := do
  let mut m := mkNameMap _
  for e in trocqEntries (← getEnv) do
    if let .relator hA _hB witName cls := e then m := m.insert hA (← mkConstWithFreshMVarLevels witName, cls)
  return m

end LeTrocq.Solver
