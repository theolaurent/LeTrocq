/-
THE GRADED RELATIONAL TRANSLATION `[·]`: the relatedness witness `[e] : 〚T〛 e ⟨e⟩` (`〚T〛 := [T].R`), on top
of the one term translation `⟨·⟩` (`Translate.term`). Two mutually-recursive halves:

  • the TYPE half (`assemble`) — a SINGLE syntax-directed pass driven by a DEMANDED output class. It walks `T`
    top-down and at each former pushes the demand through the `arrowVariance`/`forallVariance` tables to the
    minimal class each part needs, building the node with its graded combinator at exactly that class. A LEAF
    (registered atom or bound type var) reads its available class and WEAKENS to the demand. No constraint
    graph, no fixpoint — infeasibility is just a stuck `assemble` (a `Type` above the `(2a,2a)` ceiling, or a
    leaf that can't weaken).
  • the TERM half (`assembleTerm`) — the abstraction theorem `[t u] = [t] u ⟨u⟩ [u]`, bottoming at registered
    TERM primitives. A PROPOSITION is a `Sort 0` type: `[P] : PLift (P ↔ P')` is the type witness projected by
    `iffOfParam`, so there is no separate `Prop` arm.

BOUND VARIABLES ARE PINNED AT `(4,4)` (the universe combinator's inner class, independent of the capped outer
class); each use weakens down. This is what removes the fixpoint — a var's class is no longer the join of its
uses. `transfer`/`relate` are the type/term entry points.
-/
import LeTrocq.Solver
import LeTrocq.TranslateTerm
import LeTrocq.ParamCC
import Lean
open Lean Lean.Meta
namespace LeTrocq.Transfer
open LeTrocq MapClass LeTrocq.Solver

/- ===================== class/weakening helpers ===================== -/
def classToExpr : MapClass → Expr
  | .map0 => mkConst ``MapClass.map0 | .map1 => mkConst ``MapClass.map1
  | .map2a => mkConst ``MapClass.map2a | .map2b => mkConst ``MapClass.map2b
  | .map3 => mkConst ``MapClass.map3 | .map4 => mkConst ``MapClass.map4

/-- proof of `MapClass.le t s = true` (used for weakening and for a combinator's class cap), via `decide`. -/
def leProof (t s : MapClass) : MetaM Expr := do
  mkDecideProof (← mkEq (mkApp2 (mkConst ``MapClass.le) (classToExpr t) (classToExpr s))
                        (mkConst ``Bool.true))

/-- `Param.weaken` applied to coerce a witness `p : Param src.1 src.2 _ _` down to `tgt`. -/
def weakenTo (tgt src : ParamClass) (p : Expr) : MetaM Expr := do
  if tgt == src then return p
  mkAppM ``Param.weaken #[← leProof tgt.1 src.1, ← leProof tgt.2 src.2, p]

/-- the universe combinator for `Type w` at outer class `req`, carrying inner relation class `inner`. The
    level `w` is PINNED explicitly (`mkConst … [w]`) because it is phantom in `paramTypeAtInner`'s result —
    no argument carries it, so `mkAppM` could only leave it a free mvar (later wrongly zeroed). -/
def mkUniv (w : Level) (req inner : ParamClass) : MetaM Expr := do
  unless MapClass.le req.1 map2a && MapClass.le req.2 map2a do
    throwError "assemble: `Type` at {repr req} exceeds the universe ceiling (2a) — needs univalence"
  let hm ← leProof req.1 map2a
  let hn ← leProof req.2 map2a
  return mkAppN (mkConst ``paramTypeAtInner [w])
    #[classToExpr req.1, classToExpr req.2, classToExpr inner.1, classToExpr inner.2, hm, hn]

/-- recover `w` from a universe-binder domain `Type w = Sort (w+1)`; a bare `Sort u`/`Prop` domain is out of
    scope for the `Type`-universe path. -/
def typeLevelOf (dom : Expr) : MetaM Level := do
  let .sort l := dom | throwError "assemble: universe-binder domain is not a sort: {dom}"
  match (← instantiateLevelMVars l) with
  | .succ w => return w
  | l       => throwError "assemble: universe binder over `Sort {l}` — only `Type w` domains supported"

/-- the INNER class of every universe combinator: the strength of the `Param p q A A'` a bound type variable is
    offered at. Pinned `(4,4)`: it is the top, independent of the capped outer class, and
    weakens to satisfy every use — which is exactly what lets a bound variable have a fixed class (no fixpoint).
    `paramIdAt (4,4)` is `paramRefl` weakened, so this needs no axiom. -/
def innerClass : ParamClass := (map4, map4)

/-- split a target Π/arrow `A' → B'` / `∀ x', B'` into `(some A', some rawBody)` (the body keeps its loose
    bvar 0 for a dependent Π); `none` target ⇒ `(none, none)` (synth). Errors if a present target is not a
    Π-shape — the crisp "shape mismatch" for e.g. `… to (Nat × Nat)` against an arrow. -/
def splitForallTgt (tgt? : Option Expr) : MetaM (Option Expr × Option Expr) := do
  match tgt? with
  | none => return (none, none)
  | some t => match (← whnf t) with
    | .forallE _ d b _ => return (some d, some b)
    | other => throwError "transfer: target {other} is not a function type (expected a Π/arrow)"

/- ===================== the graded relational translation `[·]` ===================== -/
/-- the shared `[·]` environment, threaded through EVERY arm (both halves): `fvar ↦ (counterpart x',
    witness-or-relatedness)`. For a TYPE binder the third slot is the bound type's `Param` *witness* at inner
    class `(4,4)` (the leaf rule weakens it to each use; a term-primitive consuming the bound type is fed its
    `.R`); for a TERM binder it is the bare relatedness `xR`. The two never confuse the type/term judgments:
    a type variable's `fvar` has a `Sort` type, a term variable's does not. -/
abbrev SEnv := List (FVarId × Expr × Expr)

/-- project an `SEnv` to the counterpart environment `⟨·⟩` (`Translate.term`) consumes. -/
def SEnv.toTEnv (s : SEnv) : LeTrocq.Translate.TEnv := s.map (fun e => (e.1, e.2.1))

/-- registries + the `⟨·⟩` context, threaded through every arm of `[·]` (built once per top-level call). -/
structure Reg where
  atoms    : NameMap (NameMap (Expr × Expr × ParamClass))
  atomPref : NameMap Name
  consts   : NameMap Expr
  ctx      : LeTrocq.Translate.Ctx

/-- does `e` bind over a `Sort` (a `∀`/`λ` whose domain is a universe)? Such a type/term is EXCLUDED from the
    whole-diagonal short-circuit: a universe quantifier must keep its parametric witness (the free theorem),
    not collapse to the discrete equality relation `paramRefl` carries. -/
def containsSortBinder (e : Expr) : Bool :=
  (e.find? fun s => match s with
    | .forallE _ d _ _ => d.isSort
    | .lam _ d _ _     => d.isSort
    | _ => false).isSome

/-- run `k`, returning `none` (state restored) if it throws — for the speculative counterpart used by the
    diagonal check, which must not fail the whole pass when `⟨·⟩` stalls. -/
def tryCounterpart (k : MetaM Expr) : MetaM (Option Expr) := do
  try return some (← k) catch _ => return none

/-- `isDefEq a b`, but `false` (never an error) if it throws — the diagonality check is speculative and must
    tolerate a raw input expr the structural path handles syntactically (e.g. `mkConst ``List` with no levels). -/
def diagEq? (a b : Expr) : MetaM Bool := do
  try isDefEq a b catch _ => return false

mutual
/-- `[·]` on a TYPE — the syntax-directed, DEMAND-driven half: walk `T` top-down and build its `Param` witness
    DIRECTLY at the demanded class `dem`, pushing the demand through `arrowVariance`/`forallVariance` to the minimal
    class each part needs. ONE environment `senv` (`fvar ↦ (counterpart, witness/relatedness)`) is threaded through
    BOTH halves — every in-scope binder, type and term alike, lives there. A relator's TERM arguments go to
    `assembleTerm` (`[t u] = [t] u ⟨u⟩ [u]`). Bound type variables and registered atoms are leaves: they read their
    available class and weaken to `dem`. -/
partial def assemble (reg : Reg) (senv : SEnv) (T : Expr) (dem : ParamClass)
    (tgt? : Option Expr) : MetaM Expr := do
  -- WHOLE-DIAGONAL short-circuit: a type that transfers to ITSELF is built as the generic `paramRefl` (relation
  -- `PLift (a=b)`, map `id`), weakened to the demand — no structural descent, no per-type registration. Skipped
  -- for a bare sort / a universe binder (those keep their parametric witness). "Transfers to itself" means: a
  -- DEMANDED target defeq `T` (check mode), or — with no target — the synthesised counterpart `⟨T⟩` is `T`.
  if !T.isSort && !containsSortBinder T then
    let diag ← match tgt? with
      | some t => diagEq? T t
      | none   => match ← tryCounterpart (LeTrocq.Translate.term reg.ctx senv.toTEnv T none) with
                  | some t' => diagEq? T t'
                  | none    => pure false
    if diag then
      return ← weakenTo dem (map4, map4) (← mkAppM ``paramRefl #[T])
  match T with
  | .const name _ =>
      -- LEAF: a registered base atom, available at its registered class `regC`; weaken to the demand.
      -- CHECK mode: select the base for the demanded TARGET head; SYNTH: the preferred (last-registered) target.
      let some tgtMap := reg.atoms.find? name | throwError "assemble: atom {name} not registered"
      let tgtHead ← match tgt? with
        | some t => match (← whnf t).getAppFn.constName? with
            | some h => pure h
            | none   => throwError "assemble: target type {t} has no head constant"
        | none => match reg.atomPref.find? name with
            | some h => pure h
            | none   => throwError "assemble: atom {name} has no preferred target"
      let some (_, wit, regC) := tgtMap.find? tgtHead
        | throwError "assemble: no registered base {name} ≃ {tgtHead}"
      weakenTo dem regC wit
  | .fvar id =>
      -- LEAF: a bound TYPE variable, offered at inner class `(4,4)`; weaken its witness to the demand.
      let some (_, _, aR) := senv.find? (·.1 == id)
        | throwError "assemble: unbound type variable {T}"
      weakenTo dem innerClass aR
  | .sort lvl => do
      -- `Prop` (Sort 0) reaches the full `(4,4)` via `paramProp` (completeness = `propext`, coherence free by
      -- proof irrelevance); `Type w` (Sort (w+1)) uses the level-`w` universe combinator at `dem`, capped at the
      -- `(2a,2a)` no-univalence ceiling (`mkUniv`), carrying the bound variable at inner class `(4,4)`.
      match (← instantiateLevelMVars lvl) with
      | .zero   => mkAppM ``paramPropAt #[classToExpr dem.1, classToExpr dem.2]
      | .succ w => mkUniv w dem innerClass
      | l       => throwError "assemble: unsupported sort `Sort {l}` (only `Prop` / `Type w`)"
  | .forallE n A B _ => do
      -- split the TARGET Π/arrow (if any): `domTgt?` for the domain, `bodyTgt?` (raw, loose bvar) for the codomain.
      let (domTgt?, bodyTgt?) ← splitForallTgt tgt?
      if B.hasLooseBVar 0 then
        match A with
        | .sort _ => do
            -- `∀ A : Type, B` (type-domain Π). Domain via the universe combinator at `forallVariance(dem).1`, inner `(4,4)`;
            -- codomain family under the binder at `forallVariance(dem).2`, with `A` recorded in `senv` as a `(4,4)` type var.
            let (domDem, codDem) := forallVariance dem
            let w ← typeLevelOf A
            let domWit ← mkUniv w domDem innerClass
            let pb ← withLocalDeclD n A fun a =>
              withLocalDeclD (n.appendAfter "'") A fun a' => do
                let raaTy ← mkAppM ``Param.R #[domWit, a, a']
                withLocalDeclD (n.appendAfter "R") raaTy fun aR => do
                  mkLambdaFVars #[a, a', aR]
                    (← assemble reg ((a.fvarId!, a', aR) :: senv) (B.instantiate1 a) codDem
                        (bodyTgt?.map (·.instantiate1 a')))
            mkAppM ``paramForall #[classToExpr dem.1, classToExpr dem.2, domWit, pb]
        | _ => do
            -- `∀ x : T, B` (term-domain Π over ANY buildable domain `T`). Build `T`'s witness at `forallVariance(dem).1`,
            -- read the two sides `T`/`T'` off its `Param` type, and check the body at `forallVariance(dem).2` with `x` a
            -- TERM variable whose relatedness is `domWit.R x x'`.
            let (domDem, codDem) := forallVariance dem
            let domWit ← assemble reg senv A domDem domTgt?
            let domTy := (← whnf (← instantiateMVars (← inferType domWit))).getAppArgs
            let pb ← withLocalDeclD n domTy[2]! fun x =>
              withLocalDeclD (n.appendAfter "'") domTy[3]! fun x' => do
                let xRTy ← mkAppM ``Param.R #[domWit, x, x']
                withLocalDeclD (n.appendAfter "R") xRTy fun xR => do
                  mkLambdaFVars #[x, x', xR]
                    (← assemble reg ((x.fvarId!, x', xR) :: senv) (B.instantiate1 x) codDem
                        (bodyTgt?.map (·.instantiate1 x')))
            mkAppM ``paramForall #[classToExpr dem.1, classToExpr dem.2, domWit, pb]
      else
        -- `A → B` (non-dependent arrow). Parts at `arrowVariance(dem)`.
        let (domDem, codDem) := arrowVariance dem
        mkAppM ``paramArrow
          #[classToExpr dem.1, classToExpr dem.2,
            ← assemble reg senv A domDem domTgt?,
            ← assemble reg senv (B.instantiate1 (mkConst ``True)) codDem
                (bodyTgt?.map (·.instantiate1 (mkConst ``True)))]
  | e@(.app ..) => do
      -- the abstraction theorem `[head a₁ … aₙ] = [head] a₁ ⟨a₁⟩ [a₁] … aₙ ⟨aₙ⟩ [aₙ]`, then WEAKEN to `dem`.
      -- Arguments come from the TERM (`getAppArgs`); routing (type/family/term) from the relator's `relatorArgKinds`.
      -- A TYPE arg's `Param` is assembled at the relator's declared arg class; a FAMILY arg's is the `Param` family
      -- `fun a a' aR => ⟨B a ≃ B' a'⟩`; a TERM arg's `(⟨aᵢ⟩, [aᵢ])` come from the term-half `⟨·⟩`/`[·]` over `senv`.
      let some head := e.getAppFn.constName? | throwError "assemble: application head {e.getAppFn} is not a constant"
      let some relator0 := reg.consts.find? head | throwError "assemble: constant {head} not registered"
      -- every relator is GRADED: specialize it to the demanded output class FIRST; its residual argument
      -- classes are then `variance dem` (read below by `relatorArgKinds`), and the result is already at `dem`.
      let relator := mkAppN relator0 #[classToExpr dem.1, classToExpr dem.2]
      let kinds ← relatorArgKinds relator
      let args := e.getAppArgs
      unless args.size == kinds.size do
        throwError "assemble: relator {head} takes {kinds.size} arguments but is applied to {args.size}"
      -- CHECK mode: the target `F' a₁' …` supplies each argument's target `aᵢ'` (positionally aligned with
      -- `args`). NO `whnf` — it would unfold a reducible former/predicate (`Pos'`) and break the arg alignment
      -- with the source `args` (which are read raw off `e`).
      let tgtArgs? ← tgt?.mapM fun t => do
        let ta := (← instantiateMVars t).getAppArgs
        unless ta.size == args.size do
          throwError "assemble: target {t} of {head} has {ta.size} arguments but expected {args.size}"
        return ta
      let mut argExprs : Array Expr := #[]
      let mut argWits : Array (Option Expr) := Array.replicate args.size none  -- each TYPE arg's witness, by index
      for i in [0 : args.size] do
        let arg := args[i]!
        let argTgt? := tgtArgs?.map (·[i]!)
        match kinds[i]! with
        | .type cls => do                                  -- TYPE arg: build its `Param` at the relator's class
            let tR ← assemble reg senv arg cls argTgt?
            let tgt := (← whnf (← instantiateMVars (← inferType tR))).getAppArgs[3]!
            argExprs := argExprs ++ #[arg, tgt, tR]
            argWits := argWits.set! i (some tR)
        | .family cls domIdx => do                         -- FAMILY arg: build the `Param` family + its B-side
            let some paWit := argWits[domIdx]!
              | throwError "assemble: family argument {i} of {head} has no domain type argument (#{domIdx})"
            let paTy := (← whnf (← instantiateMVars (← inferType paWit))).getAppArgs
            let (famB', pbWit) ← withLocalDeclD `a paTy[2]! fun a => withLocalDeclD `a' paTy[3]! fun a' => do
              let aRTy ← mkAppM ``Param.R #[paWit, a, a']
              withLocalDeclD `aR aRTy fun aR => do
                -- the target family `B'` applied to this fiber's counterpart `a'` gives the body target.
                let bodyWit ← assemble reg ((a.fvarId!, a', aR) :: senv) (arg.beta #[a]) cls
                  (argTgt?.map (·.beta #[a']))
                -- the B-side family `B' : A' → Type` must depend only on `a'`, never on `a`/`aR`.
                let bside := (← whnf (← instantiateMVars (← inferType bodyWit))).getAppArgs[3]!
                if bside.hasAnyFVar (fun id => id == a.fvarId! || id == aR.fvarId!) then
                  throwError "assemble: family B-side depends on the element/proof — unsupported dependent family in {head}"
                return (← mkLambdaFVars #[a'] bside, ← mkLambdaFVars #[a, a', aR] bodyWit)
            argExprs := argExprs ++ #[arg, famB', pbWit]
        | .term => do                                      -- TERM arg: counterpart `⟨a⟩` + relatedness `[a]`
            -- CHECK mode: the arg's target TYPE is the type of the target-side counterpart `aᵢ'`.
            let termTgt? ← argTgt?.mapM (inferType ·)
            let a' ← LeTrocq.Translate.term reg.ctx senv.toTEnv arg termTgt?
            let aR ← assembleTerm reg senv arg termTgt?
            argExprs := argExprs ++ #[arg, a', aR]
      -- applied positionally (`mkAppN` fills implicit binders too, e.g. a predicate's `{A A'}`); the relators
      -- are monomorphic so no universe grounding is needed. Already at `dem`, so no final weakening.
      return mkAppN relator argExprs
  | e => throwError "assemble: unsupported type {e}"

/-- `[·]` on a TYPE embedded in a term: its `Param` witness, at the trivial class `(0,0)` — a term position
    consumes only the relation `.R`, which is grade-invariant, so the cheapest class suffices. The ambient `senv`
    is threaded in so a DEPENDENT type resolves — e.g. `Boxed b` / `Vec n` with `b`/`n` bound by an outer λ (the
    bound term supplies its relatedness), or a type over an outer λ-bound TYPE variable (its `(4,4)` witness sits
    in `senv`, and `assemble`'s leaf rule weakens it). -/
partial def assembleType (reg : Reg) (senv : SEnv) (T : Expr) : MetaM Expr :=
  assemble reg senv T (map0, map0) none

/-- `〚·〛 := [·].R` (`〚A〛 := [A].R`): the RELATION of a type `T`, projected off the graded witness
    `[·]` (`assembleType`) builds. All a TERM position ever consumes of a type, and grade-invariant — so
    `assembleType`'s cheapest `(0,0)` witness suffices. -/
partial def assembleRel (reg : Reg) (senv : SEnv) (T : Expr) : MetaM Expr := do
  mkAppM ``Param.R #[← assembleType reg senv T]

/-- `[·]` on a TERM (the abstraction theorem): its relatedness `[e] : 〚T〛 e ⟨e⟩`. Counterparts `⟨·⟩` come
    from `Translate.term`; a TYPE-valued sub-term contributes its relation `(assembleType …).R`. A PROPOSITION
    `P` is just a `Sort 0` type: its relatedness `[P] : 〚Prop〛 P P' = PLift (P ↔ P')` is the `(1,1)` `Param`
    witness the relator path builds, projected via `iffOfParam` — no separate `Prop` arm. Bottoms out at
    registered TERM primitives (`ctx.terms`). -/
partial def assembleTerm (reg : Reg) (senv : SEnv) (e : Expr) (tgt? : Option Expr) : MetaM Expr := do
  let ty ← inferType e
  if let .sort lvl := ty then
    if (← instantiateLevelMVars lvl) == levelZero then
      -- a PROPOSITION: build its `(1,1)` `Param` witness through the ordinary relator/type path, then project
      -- to `PLift (P ↔ P')`. A bound `Prop` variable's relatedness already sits in `senv` as that `PLift`.
      match e with
      | .fvar id =>
          match senv.find? (·.1 == id) with
          | some (_, _, w) => return w
          | none => throwError "assemble: unbound proposition variable {e}"
      | _ =>
          let w ← assemble reg senv e (map1, map1) tgt?
          return ← mkAppM ``PLift.up #[← mkAppM ``iffOfParam #[w]]
    else return ← assembleRel reg senv e
  -- WHOLE-DIAGONAL short-circuit: a term that transfers to ITSELF has relatedness `PLift.up rfl` (`[e] : 〚T〛 e e`
  -- with `〚T〛 = PLift (a=b)`, from the diagonal `assemble` of its type). Gated on BOTH the TYPE transferring
  -- diagonally (a demanded target defeq `ty`, or synth `⟨ty⟩ ≡ ty`) AND the term's counterpart being itself
  -- (`⟨e⟩ ≡ e`) — the latter rejects a term over a TRANSFERRED bound variable whose type is nonetheless diagonal.
  -- also exclude a term whose TYPE is polymorphic (a bare constructor `@List.cons : ∀{α}, …`): its diagonal
  -- relatedness is a FUNCTION, not `PLift.up rfl`, and collapsing it would break the application spine.
  if !containsSortBinder e && !containsSortBinder ty then
    let tyDiag ← match tgt? with
      | some t => diagEq? ty t
      | none   => match ← tryCounterpart (LeTrocq.Translate.term reg.ctx senv.toTEnv ty none) with
                  | some ty' => diagEq? ty ty'
                  | none     => pure false
    if tyDiag then
      if let some e' ← tryCounterpart (LeTrocq.Translate.term reg.ctx senv.toTEnv e tgt?) then
        if ← diagEq? e e' then
          return ← mkAppM ``PLift.up #[← mkEqRefl e]
  if let some n := LeTrocq.Translate.natNumeral? e then
    if (← whnf ty).isConstOf ``Nat then return ← assembleTerm reg senv (LeTrocq.Translate.natExpr n) tgt?
  match e with
  | .fvar id =>
      match senv.find? (·.1 == id) with
      | some (_, _, xR) => return xR
      | none => throwError "assemble: unbound variable {e}"
  | .const c _ =>
      -- CHECK mode: select the primitive's relatedness for the demanded target type; SYNTH: the preferred.
      let key? := (← whnf (tgt?.getD e)).getAppFn.constName?
      match reg.ctx.terms.find? c with
      | some tgtMap =>
          let some h := (match tgt? with | some _ => key? | none => reg.ctx.termPref.find? c)
            | throwError "assemble: term {c} has no target"
          let some (_, wit) := tgtMap.find? h
            | throwError "assemble: no relatedness for term {c} at target {h}"
          return wit
      | none => throwError "assemble: unregistered constant {c}"
  | e@(.app ..) => do
      match tgt? with
      | none =>
          let f := e.appFn!; let a := e.appArg!
          let fR ← assembleTerm reg senv f none
          let a' ← LeTrocq.Translate.term reg.ctx senv.toTEnv a none
          let aR ← assembleTerm reg senv a none
          return mkApp3 fR a a' aR
      | some _ =>
          -- SPINE (`[h a₁ … aₙ] = [h] a₁ ⟨a₁⟩ [a₁] …`): resolve the head against the result target, then take
          -- each argument's target from the head counterpart's domain type (dependent codomains via `⟨aᵢ⟩`).
          let fn := e.getAppFn
          let mut acc ← assembleTerm reg senv fn tgt?
          let fn' ← LeTrocq.Translate.term reg.ctx senv.toTEnv fn tgt?
          let mut ty ← inferType fn'
          for a in e.getAppArgs do
            let (dom, cod) ← match (← whnf ty) with
              | .forallE _ d b _ => pure (d, b)
              | other => throwError "assemble: head counterpart type {other} is not a function"
            let a' ← LeTrocq.Translate.term reg.ctx senv.toTEnv a (some dom)
            let aR ← assembleTerm reg senv a (some dom)
            acc := mkApp3 acc a a' aR; ty := cod.instantiate1 a'
          return acc
  | .lam n A b _ => do
      let (domTgt?, bodyTgt?) ← LeTrocq.Translate.splitPi? tgt?
      let A' ← LeTrocq.Translate.term reg.ctx senv.toTEnv A domTgt?
      -- the bound variable's relatedness is `〚A〛 = [A].R`: for a type binder the parametricity relation, for
      -- a term/base binder the bare relatedness. (`assembleRel` projects it off the graded witness `[A]`.)
      let relA ← assembleRel reg senv A
      withLocalDeclD n A fun x =>
      withLocalDeclD (n.appendAfter "'") A' fun x' =>
      withLocalDeclD (n.appendAfter "R") (mkApp2 relA x x') fun xR => do
        mkLambdaFVars #[x, x', xR]
          (← assembleTerm reg ((x.fvarId!, x', xR) :: senv) (b.instantiate1 x)
            (bodyTgt?.map (·.instantiate1 x')))
  | e => throwError "assemble: unsupported term {e}"
end

/-- the registries + `⟨·⟩` context, built once from the `@[trocq]` environment extension. -/
def mkReg : MetaM Reg := do
  let (atoms, atomPref) ← Solver.buildAtomPairs
  return { atoms, atomPref, consts := ← Solver.buildConsts, ctx := ← LeTrocq.Translate.buildCtx }

/-- default any genuinely-free residual universe mvars (e.g. the universe combinator's relation level, or a
    universe-poly registered witness's level) to 0 — they are unconstrained, so any level is sound. -/
def defaultFreeLevels (wit : Expr) : MetaM Expr := do
  let wit ← instantiateMVars wit
  let st := Lean.collectLevelMVars (Lean.collectLevelMVars {} wit) (← instantiateMVars (← inferType wit))
  for mid in st.result do
    unless (← isLevelMVarAssigned mid) do assignLevelMVar mid levelZero
  instantiateMVars wit

/-- `[T]@root` for a TYPE: assemble the witness DIRECTLY at `root` in one demand-driven pass — every node built
    by the graded combinator at the minimal class the demand pushes down. Drives `transfer%`/`trocq`. -/
partial def transfer (e : Expr) (root : ParamClass) (target? : Option Expr := none) : MetaM Expr := do
  defaultFreeLevels (← assemble (← mkReg) [] e root target?)

/-- `[t]` for a TERM: its relatedness by the abstraction theorem. Drives `relate%`. -/
partial def relate (e : Expr) : MetaM Expr := do
  defaultFreeLevels (← assembleTerm (← mkReg) [] e none)

end LeTrocq.Transfer
