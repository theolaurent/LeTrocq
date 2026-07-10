/-
The TERM TRANSLATION `⟨·⟩` (the counterpart translation): for a term/type `e`, the B-side counterpart `⟨e⟩` —
`e` rebuilt leaf-by-leaf over `B`, bottoming at registered PRIMITIVES; an unregistered head is an ERROR.

  ⟨c⟩        = registered counterpart (term primitive / type former / Prop predicate)
  ⟨x⟩        = x'                                       (bound variable's counterpart)
  ⟨f a⟩      = ⟨f⟩ ⟨a⟩       ⟨fun x=>b⟩ = fun x'=>⟨b⟩       ⟨Πx:A. B⟩ = Πx':⟨A⟩. ⟨B⟩

The other half is the RELATEDNESS `[e] : 〚T〛 e ⟨e⟩`, the graded `[·]` in `LeTrocq.Driver.Transfer` (the sole
consumer of `⟨·⟩`). The shared `Ctx`/`buildCtx`/`sym*` below serve both.
-/
import LeTrocq.Combinators
import LeTrocq.Driver.Registry
import Lean
open Lean Lean.Meta
namespace LeTrocq.Counterpart

/-- the `⟨·⟩` registration (COUNTERPARTS only): type formers/bases/relators ↦ B-side head; term primitives ↦
    (B-term, relatedness witness) — `⟨·⟩` uses only the first component, `[·]` reads the relatedness. A `Prop`'s
    counterpart comes from its RELATOR entry in `types`. `typePref`/`termPref` are the per-head PREFERRED
    (last-registered) counterpart used in synth mode. -/
structure Ctx where
  types    : NameMap (NameMap Expr)
  typePref : NameMap Name
  terms    : NameMap (NameMap (Expr × Expr))
  termPref : NameMap Name
  -- GROUND closed-type equivalences (`List Unit ↦ Nat`), HEAD-INDEXED `srcHead ↦ #[(srcTy, tgtTy)]`, matched
  -- WHOLE by `isDefEq`. Both directions stored separately; the leaf rule keeps the LAST match.
  ground   : NameMap (Array (Expr × Expr))
  -- GROUND TERMS: partial-application patterns (`@List.cons Unit ()`), HEAD-INDEXED, matched WHOLE by `isDefEq`.
  -- `⟨pattern⟩ = tgtPrefix` (`Nat.succ`); the app spine applies it to the translated remaining args. `wit` is
  -- the relatedness the term half feeds that spine.
  groundTerms : NameMap (Array (Expr × Expr × Expr))

/-- counterpart environment for `⟨·⟩`: `fvar ↦ x'`, the bound variable's B-side counterpart. -/
abbrev TEnv := List (FVarId × Expr)

/-- recognize a numeral — a raw `.lit (.natVal n)` or `@OfNat.ofNat _ (lit n) _` — as `n`. The caller must
    additionally check the type is `Nat` (the type argument here may be unreduced). -/
def natNumeral? (e : Expr) : Option Nat :=
  if let some n := e.rawNatLit? then some n
  else if e.getAppFn.isConstOf ``OfNat.ofNat then
    let args := e.getAppArgs
    if args.size == 3 then args[1]!.rawNatLit? else none
  else none

/-- expand `n` to its `Nat.succ`/`Nat.zero` normal form, so a numeral leaf reduces to registered primitives. -/
def natExpr : Nat → Expr
  | 0 => mkConst ``Nat.zero
  | n + 1 => mkApp (mkConst ``Nat.succ) (natExpr n)

/-- sentinel target-key for term primitives whose result type is NOT constant-headed (a recursor polymorphic
    in its motive). Not target-selectable, only reachable via the synth default, so all share this one key. -/
def polyResultKey : Name := `_LeTrocq.polyResult

/-- head of a term primitive's RESULT type — the target-TYPE key it's filed under (`Unary.s` ↦ `Unary`,
    `List.cons` ↦ `List`); a non-constant conclusion ↦ `polyResultKey`. -/
def resultTypeHead (e : Expr) : MetaM Name := do
  forallTelescopeReducing (← inferType e) fun _ concl => do
    return concl.getAppFn.constName?.getD polyResultKey

/-- split a target Π/arrow into `(some domain, some rawBody)`; lenient — a `none` or non-Π target ⇒
    `(none, none)` (fall back to synth). Used for the counterpart of a λ / Π under a demanded target. -/
def splitPi? (tgt? : Option Expr) : MetaM (Option Expr × Option Expr) := do
  match tgt? with
  | some t => match (← whnf t) with
    | .forallE _ d b _ => return (some d, some b)
    | _ => return (none, none)
  | none => return (none, none)

/-- `⟨·⟩` — THE TERM TRANSLATION: rebuild `e`'s B-side counterpart leaf by leaf. A registered head maps to its
    counterpart (`Nat.succ ↦ Unary.s`, `List ↦ List`, a `Prop` predicate `p ↦ p'`); a bound variable to `x'`;
    Π/λ/app/sort structurally; a `Nat` numeral through its `succ`/`zero` normal form. An unregistered head is
    an ERROR — never unfolds. An optional `tgt?` (the demanded counterpart TYPE) selects registered heads
    TYPE-DIRECTEDLY (`Nat.zero ↦ Unary.z` at `Unary`, `↦ Nat.zero` at `Nat`), destructured down an application
    spine. Produces ONLY the counterpart; `[·]` calls back here for every counterpart it needs. -/
partial def term (ctx : Ctx) (env : TEnv) (e : Expr) (tgt? : Option Expr) :
    MetaM Expr := do
  -- GROUND closed-type equivalence (`⟨List Unit⟩ = Nat`): matched WHOLE (head-indexed, `isDefEq`), so it beats
  -- the structural descent below. Only type-EXPRESSIONS match (a term is never `isDefEq` to its type). Last match wins.
  if let some h := e.getAppFn.constName? then
    if let some cands := NameMap.find? ctx.ground h then
      let mut hit : Option Expr := none
      for (srcTy, tgtTy) in cands do
        if ← diagEq? e srcTy then
          let ok ← match tgt? with
            | some t => diagEq? t tgtTy
            | none   => pure true
          if ok then hit := some tgtTy
      if let some tgtTy := hit then return tgtTy
  -- GROUND TERM: `e` (a partial application, exposed as an appFn subterm by the `.app` recursion) matches a
  -- registered pattern WHOLE ⇒ counterpart is the target prefix (`Nat.succ`). Arity pre-filter, then `isDefEq`.
  if let some h := e.getAppFn.constName? then
    if let some cands := NameMap.find? ctx.groundTerms h then
      for (patSrc, tgtTerm, _wit) in cands do
        if e.getAppNumArgs == patSrc.getAppNumArgs && (← diagEq? e patSrc) then
          return tgtTerm
  if let some n := natNumeral? e then
    if (← whnf (← inferType e)).isConstOf ``Nat then return ← term ctx env (natExpr n) tgt?
  match e with
  | .fvar id =>
      match env.find? (·.1 == id) with
      | some (_, x') => return x'
      | none => throwError "translate: unbound variable {e}"
  | .const c _ =>
      -- registry lookup: term primitives, then types. CHECK mode selects by the target head; SYNTH mode uses the pref.
      let key? := (← whnf (tgt?.getD e)).getAppFn.constName?
      if let some tgtMap := ctx.terms.find? c then
        let some h := (match tgt? with | some _ => key? | none => ctx.termPref.find? c)
          | throwError "translate: term {c} has no target"
        match tgtMap.find? h with
        | some (b, _) => return b
        | none =>
            -- DIAGONAL target: the demanded type is the source's own type ⇒ `c` is its own counterpart.
            if (← (tgt?.mapM fun t => do isDefEq (← inferType e) t)).getD false then return e
            else throwError "translate: no counterpart for term {c} at target {h}"
      else if let some tgtMap := ctx.types.find? c then
        let some h := (match tgt? with | some _ => key? | none => ctx.typePref.find? c)
          | throwError "translate: type {c} has no target"
        match tgtMap.find? h with
        | some b => return b
        | none =>
            if (← (tgt?.mapM fun t => do isDefEq e t)).getD false then return e
            else throwError "translate: no counterpart for type {c} at target {h}"
      else
        -- UNREGISTERED constant ⇒ its own counterpart (the diagonal). Soundness is upstream: `Transfer`'s
        -- whole-diagonal short-circuit relies on this only after verifying the surrounding type/term is diagonal.
        return e
  | e@(.app ..) => do
      match tgt? with
      | none => return .app (← term ctx env e.appFn! none) (← term ctx env e.appArg! none)
      | some _ =>
          -- SPINE: resolve the head against the result target, then take each arg's target from the head
          -- counterpart's domain, threading dependent codomains via the built counterpart.
          let fn := e.getAppFn
          let mut acc ← term ctx env fn tgt?
          let mut ty ← inferType acc
          for a in e.getAppArgs do
            let (dom, cod) ← match (← whnf ty) with
              | .forallE _ d b _ => pure (d, b)
              | other => throwError "translate: head counterpart type {other} is not a function"
            let a' ← term ctx env a (some dom)
            acc := .app acc a'; ty := cod.instantiate1 a'
          return acc
  | .sort _ => return e
  | .lam n A b _ => do
      let (domTgt?, bodyTgt?) ← splitPi? tgt?
      let A' ← term ctx env A domTgt?
      withLocalDeclD n A fun x => withLocalDeclD (n.appendAfter "'") A' fun x' =>
        return ← mkLambdaFVars #[x'] (← term ctx ((x.fvarId!, x') :: env) (b.instantiate1 x)
          (bodyTgt?.map (·.instantiate1 x')))
  | .forallE n A B _ => do
      let (domTgt?, bodyTgt?) ← splitPi? tgt?
      let A' ← term ctx env A domTgt?
      withLocalDeclD n A fun x => withLocalDeclD (n.appendAfter "'") A' fun x' =>
        return ← mkForallFVars #[x'] (← term ctx ((x.fvarId!, x') :: env) (B.instantiate1 x)
          (bodyTgt?.map (·.instantiate1 x')))
  | e => throwError "translate: unsupported {e}"

/-- telescope a primitive's type into triples, and run `k` with the binders `xs` and their VALUE-SWAPPED
    reordering `[a',a,aRel, …]` (the relatedness slot stays put). The shared frame of the backward builders. -/
def withSwappedTriples (what : String) (wit : Expr) (k : Array Expr → Array Expr → MetaM Expr) :
    MetaM Expr := do
  forallTelescope (← inferType wit) fun xs _ => do
    let mut swapped : Array Expr := #[]
    for (a, a', aRel) in ← chunkTriples what wit xs do
      swapped := swapped.push a' |>.push a |>.push aRel     -- swap the value pair, keep the relatedness
    k xs swapped

/-- swap the (A-value, B-value) in each triple of a term primitive, giving the BACKWARD-direction combinator:
    `cWit : ∀ a a' (aRel : R a a') …, R (c …) (c' …)` ↦ `fun a' a aRel … => cWit a a' aRel …`. The relatedness
    keeps type `R a a'`, defeq to the reverse's `R.sym a' a`, so the same proof serves — only the values swap. -/
def symPrimitive (wit : Expr) : MetaM Expr :=
  withSwappedTriples "term primitive" wit fun xs swapped => mkLambdaFVars swapped (mkAppN wit xs)

/-- the REVERSE of a STRUCTURE-relation INSTANCE witness `wit : SR Θ p p'` (a `GroupR`-style correspondence
    between two SPECIFIC instances, `intGroup ↔ boolGroup`). Rebuild `SR.mk <Θ reversed> p' p <fields
    symmetrized>` at `SR Θ' p' p`: each theme type-triple `(T, T', RT)` ↦ `(T', T, flip RT)`, `p`/`p'` swap,
    each projection reversed by `symPrimitive`. Needed because `symPrimitive` on the whole zero-triple witness
    returns it unchanged (wrong orientation). `none` unless `wit` is a closed instance with whole type-triples. -/
def symStructure (wit : Expr) : MetaM (Option Expr) := do
  forallTelescope (← inferType wit) fun bs concl => do
    unless bs.isEmpty do return none                          -- only a closed instance (no leading binders)
    let some srName := concl.getAppFn.constName? | return none
    let env ← getEnv
    unless isStructure env srName do return none
    let srCtor := getStructureCtor env srName
    let nP := srCtor.numParams
    if nP < 2 || (nP - 2) % 3 != 0 then return none            -- need `p p'` + a whole number of type-triples
    let args := concl.getAppArgs
    unless args.size == nP do return none
    let theme := args.extract 0 (nP - 2)
    let p  := args[nP - 2]!
    let p' := args[nP - 1]!
    -- reverse the theme: each type-triple `(T, T', RT)` ↦ `(T', T, flip RT)`.
    let mut revTheme : Array Expr := #[]
    for i in [0 : (nP - 2) / 3] do
      let (T, T', RT) := (theme[3*i]!, theme[3*i+1]!, theme[3*i+2]!)
      let flipRT ← withLocalDeclD `x' T' fun x' => withLocalDeclD `x T fun x =>
        mkLambdaFVars #[x', x] (mkApp2 RT x x')
      revTheme := revTheme.push T' |>.push T |>.push flipRT
    -- reverse each field via `symPrimitive`. Use the raw kernel projection `.proj` (index-based), not the
    -- projection function — `SR` may be a `class`, whose fields take the instance as `[instImplicit]`, which
    -- `mkAppM` would mis-slot.
    let mut fields : Array Expr := #[]
    for i in [0 : (getStructureFields env srName).size] do
      fields := fields.push (← symPrimitive (.proj srName i wit))
    let srMk := mkConst srCtor.name (srCtor.levelParams.map mkLevelParam)
    return some (mkAppN srMk (revTheme ++ #[p', p] ++ fields))

/-- the translation context assembled from the `@[trocq]` extension, in BOTH directions: every BASE gives a
    type relation forward and backward; every TERM primitive gives its `c ↦ c'` map forward and the swapped
    `c' ↦ c` map (via `symPrimitive`) backward. So a term over either side translates by head match. -/
def buildCtx : MetaM Ctx := do
  let mut types    : NameMap (NameMap Expr) := mkNameMap _
  let mut typePref : NameMap Name := mkNameMap _
  let mut terms    : NameMap (NameMap (Expr × Expr)) := mkNameMap _
  let mut termPref : NameMap Name := mkNameMap _
  let mut ground      : NameMap (Array (Expr × Expr)) := mkNameMap _
  let mut groundTerms : NameMap (Array (Expr × Expr × Expr)) := mkNameMap _
  -- every BASE / TERM installs in both directions, with a single preferred (last-registered) counterpart per head.
  for e in trocqEntries (← getEnv) do
    match e with
    | .base hA hB tyA tyB _witName _ =>
        -- `⟨·⟩` needs only the COUNTERPART type: `⟨A⟩ = B`, `⟨B⟩ = A`.
        let r ← insertBidirPair types typePref hA (some hB) tyB (return tyA)
        types := r.1; typePref := r.2
    | .ground hA hB tyA tyB _witName _ =>
        -- a GROUND closed-type equivalence, matched WHOLE (`isDefEq`).
        ground := ground.insert hA ((NameMap.find? ground hA |>.getD #[]).push (tyA, tyB))
        ground := ground.insert hB ((NameMap.find? ground hB |>.getD #[]).push (tyB, tyA))
    | .groundTerm hA patternA tgtB witName =>
        -- a GROUND TERM `⟨@List.cons Unit ()⟩ = Nat.succ`, matched WHOLE; `wit` is the relatedness.
        let wit ← mkConstWithFreshMVarLevels witName
        groundTerms := groundTerms.insert hA
          ((NameMap.find? groundTerms hA |>.getD #[]).push (patternA, tgtB, wit))
        -- BACKWARD `⟨tgtB⟩ = patternA`, keyed by the TARGET head, relatedness `symPrimitive`d (the spine feeds
        -- the A-side value first, so the triples must be reordered — as for a plain `.term`). Unlike `.term`
        -- (skipped when homogeneous), a ground term ALWAYS registers its reverse: even a homogeneous head like
        -- `HAdd.hAdd ↦ HAdd.hAdd` has DISTINCT patterns per side (`ℕ`-prefix vs `ZMod`-prefix), and a `trocq`
        -- goal over the B-side type reaches its operations only through this reverse (`⟨ZMod-(+)⟩ = ℕ-(+)`).
        if let some hB := tgtB.getAppFn.constName? then
          groundTerms := groundTerms.insert hB
            ((NameMap.find? groundTerms hB |>.getD #[]).push (tgtB, patternA, ← symPrimitive wit))
    | .term hA bTerm witName =>
        -- forward: source head ↦ counterpart's RESULT-TYPE head ↦ (counterpart, relatedness). Backward keyed by
        -- the B-side head (so a homogeneous constructor like `List.cons` is skipped).
        let wit ← mkConstWithFreshMVarLevels witName
        let srcTerm ← mkConstWithFreshMVarLevels hA
        let tgtTyHead ← resultTypeHead bTerm
        terms := terms.insert hA ((NameMap.find? terms hA |>.getD (mkNameMap _)).insert tgtTyHead (bTerm, wit))
        termPref := termPref.insert hA tgtTyHead
        match bTerm.constName? with
        | some hB =>
            if hB != hA then
              let srcTyHead ← resultTypeHead srcTerm
              -- backward relatedness: a structure-relation instance reverses FIELD-WISE via `symStructure`
              -- (a zero-triple instance would otherwise come back wrong-oriented); a plain primitive by `symPrimitive`.
              let bwdRel ← match ← symStructure wit with
                | some s => pure s
                | none   => symPrimitive wit
              terms := terms.insert hB ((NameMap.find? terms hB |>.getD (mkNameMap _)).insert srcTyHead
                (srcTerm, bwdRel))
              termPref := termPref.insert hB srcTyHead
        | none => pure ()
    | .typeFormer hA hB _relName =>
        -- a parameterized type former: `⟨F a⟩ = F' ⟨a⟩` via the `.app` rule. ONE entry, forward only.
        types := types.insert hA ((NameMap.find? types hA |>.getD (mkNameMap _)).insert hB
          (← mkConstWithFreshMVarLevels hB))
        typePref := typePref.insert hA hB
    | .relator hA (some hB) _witName =>
        -- a RELATOR ALSO supplies the head counterpart `P ↦ P'` — how a connective (`And ↦ And`) or `Prop`
        -- predicate (`Pos ↦ Pos'`), which have no type former, get one. Both directions; homogeneous heads coincide.
        let r ← insertBidirPair types typePref hA (some hB)
          (← mkConstWithFreshMVarLevels hB) (mkConstWithFreshMVarLevels hA)
        types := r.1; typePref := r.2
    | .relator .. => pure ()
    | .groundFormer .. => pure ()   -- no counterpart map; only its auto-derived ground-term constructors matter
  return { types, typePref, terms, termPref, ground, groundTerms }

end LeTrocq.Counterpart
