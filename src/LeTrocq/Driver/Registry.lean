/-
The `@[trocq]` REGISTRY: classify a tagged witness (`parseEntry` → `RegKind`), store it (`@[trocq]` attribute +
`trocqExt` extension, run eagerly so malformed witnesses are rejected at the tag site), and look it back up for
the driver (`buildAtomPairs`/`buildConsts`/`relatorArgKinds`). A witness is a BASE (`Param m n A B`), a RELATOR
(`∀ …, Param m n (P …) (P' …)`), a TYPEFORMER (a parameterized type's parametricity relation, concluding a
`Sort`), or a TERM primitive (relates a term head `c ↦ c'`). NOT a grading solver — grading is inline in
`Transfer.assemble`; this is only the registry side.
-/
import LeTrocq.Core.Param
import Lean
open Lean Lean.Meta
namespace LeTrocq

/-- `isDefEq a b`, but `false` (never an error) if it throws — a speculative match must tolerate a raw input
    expr the structural path handles syntactically (e.g. `mkConst ``List` with no levels). -/
def diagEq? (a b : Expr) : MetaM Bool := do
  try isDefEq a b catch _ => return false

/-- install a witness in a NESTED map `srcHead ↦ tgtHead ↦ α` (so several registrations for one source don't
    clobber), recording the PREFERRED (last-registered) target head in `pref` (the synth default). BOTH
    directions: forward `[hA][hB] := fwd` and `pref[hA] := hB` always; the backward `[hB][hA] := bwd` (a thunk,
    run only when inserted) only when `hB` is DISTINCT from `hA` — a homogeneous head like `List.cons ↦
    List.cons` needs no backward entry. -/
def insertBidirPair {α} (m : NameMap (NameMap α)) (pref : NameMap Name)
    (hA : Name) (hB? : Option Name) (fwd : α) (bwd : MetaM α) :
    MetaM (NameMap (NameMap α) × NameMap Name) := do
  let hB := hB?.getD hA
  let innerA : NameMap α := (m.find? hA).getD (mkNameMap _)
  let m : NameMap (NameMap α) := m.insert hA (innerA.insert hB fwd)
  let pref : NameMap Name := pref.insert hA hB
  if hB == hA then return (m, pref)
  let innerB : NameMap α := (m.find? hB).getD (mkNameMap _)
  let m : NameMap (NameMap α) := m.insert hB (innerB.insert hA (← bwd))
  return (m, pref.insert hB hA)

/-- the abstraction-theorem TRIPLE convention: a witness's binders come in groups of three `(a, a', aRel)` —
    A-value, B-value, relatedness. Check `xs.size % 3 == 0` and return the triples in order. The single home of
    the `3·j` indexing that `relatorArgKinds` and `symPrimitive` both walk. -/
def chunkTriples (what : String) (wit : Expr) (xs : Array Expr) : MetaM (Array (Expr × Expr × Expr)) := do
  unless xs.size % 3 == 0 do
    throwError "trocq: {what} is not in abstraction-theorem triple form ({xs.size} binders): {wit}"
  let mut ts := #[]
  for j in [0 : xs.size / 3] do
    ts := ts.push (xs[3*j]!, xs[3*j+1]!, xs[3*j+2]!)
  return ts

/-- if a term-primitive witness is a GROUND TERM — its source is a partial application (`@List.cons Unit ()`)
    with FIXED leading args before its triple values — return `(sourcePattern, targetPrefix)`; else `none` (a
    plain head primitive). The triple values must be the trailing args of each side, so stripping them leaves
    the fixed prefix; no fixed prefix (e.g. `List.cons`, bare `Nat.zero`) is `none`. -/
def groundTermPattern? (wit : Expr) (bs : Array Expr) (aSide bSide : Expr) : MetaM (Option (Expr × Expr)) := do
  let triples? ← try pure (some (← chunkTriples "term primitive" wit bs)) catch _ => pure none
  let some triples := triples? | return none
  let k := triples.size
  let aArgs := aSide.getAppArgs
  let bArgs := bSide.getAppArgs
  unless aArgs.size > k && bArgs.size ≥ k do return none          -- FIXED leading source args, and B-side has ≥ k
  unless aArgs.extract (aArgs.size - k) aArgs.size == triples.map (·.1) do return none      -- trailing = A-values
  unless bArgs.extract (bArgs.size - k) bArgs.size == triples.map (·.2.1) do return none     -- trailing = B-values
  return some (mkAppN aSide.getAppFn (aArgs.extract 0 (aArgs.size - k)),
               mkAppN bSide.getAppFn (bArgs.extract 0 (bArgs.size - k)))

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

/-- the classification of a `@[trocq]` witness. The witness is kept as its NAME (`witName`), not a baked
    `mkConst`: consumers re-create it with fresh levels (`mkConstWithFreshMVarLevels`), so universe-polymorphic
    witnesses instantiate correctly. -/
inductive RegKind
  | base       (headA headB : Name) (tyA tyB : Expr) (witName : Name) (cls : ParamClass)
  -- a GROUND base generalizes `base` from two CONSTANTS to two CLOSED types (`List Unit ≃ Nat`), matched WHOLE
  -- by `isDefEq` on `tyA`/`tyB`; `headA`/`headB` only INDEX the match, never select.
  | ground     (headA headB : Name) (tyA tyB : Expr) (witName : Name) (cls : ParamClass)
  -- a RELATOR is always GRADED: leading `(m n : MapClass)`, conclusion `Param m n (F …) (F' …)`, so its
  -- per-argument classes VARY with the demand — read by specializing, not stored here.
  | relator    (headA : Name) (headB? : Option Name) (witName : Name)
  | typeFormer (headA headB : Name) (relName : Name)
  -- a GROUND FORMER: a concrete relation between two CLOSED types (`RLUN : List Unit → Nat → Type`), NOT a
  -- relator. Registers no counterpart former (the `.ground` base handles the type); exists only so `@[trocq]`
  -- auto-derives its constructors as ground terms.
  | groundFormer (relName : Name)
  | term       (headA : Name) (bTerm : Expr) (witName : Name)
  -- a GROUND TERM generalizes `term` to a partial-application pattern (`@List.cons Unit ()`), matched WHOLE by
  -- `isDefEq` ↦ its counterpart prefix (`Nat.succ`); `witName` is the relatedness the `app` rule feeds the
  -- remaining triple. The term analogue of `.ground`, for when a constructor's counterpart drops leading args.
  | groundTerm (headA : Name) (patternA tgtB : Expr) (witName : Name)
  deriving Inhabited

/-- classify a tagged constant `w` from its type (see the kinds above). The const is built with its own
    level params (`mkConstWithLevelParams`) so a universe-polymorphic `w` telescopes without a level error. -/
def parseEntry (w : Name) : MetaM RegKind := do
  let wit ← mkConstWithLevelParams w
  forallTelescopeReducing (← inferType wit) fun bs concl => do
    let args := concl.getAppArgs
    if concl.isSort then
      -- a RELATION FORMER `F-args → F'-args' → Sort`: the two related objects are the last two binders; their
      -- head constants name the A-/B-side type formers (equal for a homogeneous type like `List`).
      unless bs.size ≥ 2 do throwError "trocq: type former {w} must relate two objects"
      let objA ← inferType bs[bs.size - 2]!
      let objB ← inferType bs[bs.size - 1]!
      -- CLOSED related objects (`List Unit`/`Nat`) ⇒ a GROUND former: only its constructors matter, no counterpart.
      -- A parameterized relator (`ListR`: objects mention the params) has fvars here and stays a `.typeFormer`.
      if !objA.hasFVar && !objB.hasFVar then return .groundFormer w
      let some hA := objA.getAppFn.constName?
        | throwError "trocq: type former {w} A-object has no head constant"
      let some hB := objB.getAppFn.constName?
        | throwError "trocq: type former {w} B-object has no head constant"
      return .typeFormer hA hB w
    else if concl.getAppFn.isConstOf ``Param then
      -- a GRADED relator concludes `Param m n (F …) (F' …)` with `m n` the leading binders themselves (not
      -- literals); detect that so the driver reads its per-argument classes by specializing to the demand.
      let structural :=
        bs.size ≥ 2 && args[0]!.isFVar && args[1]!.isFVar && args[0]! == bs[0]! && args[1]! == bs[1]!
      let graded ← if structural then pure ((← inferType bs[0]!).isConstOf ``MapClass) else pure false
      let A := args[2]!; let B := args[3]!
      if graded then
        -- the B-side head `P'` is read off the conclusion too, so the relator ALSO supplies `⟨·⟩` the counterpart
        -- `P ↦ P'` (needed for connectives / `Prop` predicates, which have no separate type former).
        let some hA := A.getAppFn.constName? | throwError "trocq: graded relator {w} has no head constant"
        return .relator hA B.getAppFn.constName? w
      -- not graded: only a CLOSED base is allowed — every parameterized relator MUST be graded now.
      if bs.isEmpty && A.isConst && B.isConst then
        -- FORBID a DIAGONAL base `A ≃ A`: a type transfers to itself automatically (`paramRefl`), so it's redundant.
        if A.constName! == B.constName! then
          throwError "trocq: refusing diagonal base {w} : {A} ≃ {A} — a type transfers to itself \
            automatically, so a diagonal registration is redundant"
        return .base A.constName! B.constName! A B w (← exprToMapClass args[0]!, ← exprToMapClass args[1]!)
      -- a CLOSED GROUND equivalence: `A`/`B` closed but at least one APPLIED (`List Unit ≃ Nat`). Heads only index.
      if bs.isEmpty && !A.hasFVar && !A.hasMVar && !B.hasFVar && !B.hasMVar then
        -- FORBID a DIAGONAL ground base `T ≃ T` (`isDefEq`) — redundant with the automatic diagonal.
        if ← withNewMCtxDepth (isDefEq A B) then
          throwError "trocq: refusing diagonal ground base {w} : {A} ≃ {B} — a closed type transfers to \
            itself automatically, so a diagonal registration is redundant"
        let some hA := A.getAppFn.constName? | throwError "trocq: ground base {w} A-side has no head constant"
        let some hB := B.getAppFn.constName? | throwError "trocq: ground base {w} B-side has no head constant"
        return .ground hA hB A B w (← exprToMapClass args[0]!, ← exprToMapClass args[1]!)
      throwError "trocq: relator {w} must be GRADED — take leading `(m n : MapClass)` and conclude `Param m n …`"
    else
      if args.size ≥ 2 then
        let aSide := args[args.size - 2]!
        let bSide := args[args.size - 1]!
        -- FORBID a DIAGONAL term primitive (`isDefEq` sides, `Nat.zero ↦ Nat.zero`) — transfers to itself
        -- automatically (`[e] := PLift.up rfl`). A parametric homogeneous head is NOT diagonal: `List.cons ↦
        -- List.cons` relates `a :: l` to `a' :: l'`, whose distinct binder fvars aren't `isDefEq`, so it passes.
        if ← withNewMCtxDepth (isDefEq aSide bSide) then
          throwError "trocq: refusing diagonal term primitive {w} — it relates {aSide} to itself; a closed \
            term transfers to itself automatically, so a diagonal registration is redundant"
        let some hA := aSide.getAppFn.constName?
          | throwError "trocq: term primitive {w} has no A-side head constant"
        -- a GROUND TERM (`@List.cons Unit () ↦ Nat.succ`, fixed leading args) vs a plain head primitive.
        if let some (patternA, tgtB) ← groundTermPattern? wit bs aSide bSide then
          return .groundTerm hA patternA tgtB w
        return .term hA bSide.getAppFn w
      else throwError "trocq: cannot classify {w} : {← inferType wit}"

/- ===================== auto-derived constructor primitives ===================== -/
/-- Derive a triple-form TERM-primitive witness for one constructor `ctorName` of a tagged parametricity
    relation, so a user need not hand-write a proxy. The constructor's binders are `params ++ [value pairs] ++
    [relatedness proofs]`; this reorders them into triples
    `fun params (v₀ v₀' r₀) … => @ctor params v₀ v₀' … r₀ …` as an aux def `ctorName.trocqPrim` (carrying the
    `levelParams`). Returns `none` (no error) when the fields aren't a whole number of triples. -/
def deriveConstructorPrim (ctorName : Name) : MetaM (Option Name) := do
  let cinfo ← getConstInfoCtor ctorName
  if cinfo.numFields % 3 != 0 then return none
  let lvls := cinfo.levelParams
  let ctor := mkConst ctorName (lvls.map mkLevelParam)
  forallTelescope (← inferType ctor) fun bs concl => do
    let params := bs.extract 0 cinfo.numParams
    let fields := bs.extract cinfo.numParams bs.size
    let k := fields.size / 3
    -- the fields are `[v₀ v₀' v₁ v₁' … r₀ r₁ …]` (values then relateds); interleave into triples.
    let vals := fields.extract 0 (2 * k)
    let rels := fields.extract (2 * k) fields.size
    let mut triples : Array Expr := #[]
    for i in [0 : k] do
      triples := (triples.push vals[2 * i]!).push vals[2 * i + 1]! |>.push rels[i]!
    let reordered := params ++ triples
    let primName := ctorName.str "trocqPrim"
    -- `addAndCompile` (not `addDecl`): the witness is a bare constructor application, so it's computable and
    -- downstream `def`s that embed it (`translate`/`relate` outputs) get compiled.
    addAndCompile <| .defnDecl {
      name        := primName
      levelParams := lvls
      type        := ← mkForallFVars reordered concl
      value       := ← mkLambdaFVars reordered (mkAppN ctor bs)
      hints       := .abbrev
      safety      := .safe }
    return some primName

/-- Build the `S.mk` TERM primitive for a STRUCTURE relation `srName`. Its constructor `SR.mk` concludes
    `SR … p p'` (NOT `S.mk`-headed), so `deriveConstructorPrim` can't read it; here we specialise
    `p := @S.mk Θ v…`, `p' := @S'.mk Θ' v'…` (the two sides may be different structures — a heterogeneous record
    equivalence) and repackage into triple form `(Θ) (v₀ v₀' vR₀) …`. Returns `none` on any unexpected shape.
    Monomorphic (`Type 0`). -/
def deriveStructureCtorPrim (srName : Name) : MetaM (Option Name) := do
  let env ← getEnv
  let srCtor := getStructureCtor env srName
  let nP := srCtor.numParams
  if nP < 2 then return none                                  -- need the two related-structure params `p p'`
  let lvls := srCtor.levelParams
  let srMk := mkConst srCtor.name (lvls.map mkLevelParam)
  forallTelescope (← inferType srMk) fun bs _ => do
    let theme     := bs.extract 0 (nP - 2)                    -- the type-triples `Θ_A Θ_B RΘ …`
    let p         := bs[nP - 2]!
    let p'        := bs[nP - 1]!
    let fieldRels := bs.extract nP bs.size                    -- one relatedness field per data field
    let pTy  ← whnf (← inferType p)
    let pTy' ← whnf (← inferType p')
    let some sName  := pTy.getAppFn.constName?  | return none   -- A-side data structure `S`
    let some sName' := pTy'.getAppFn.constName? | return none   -- B-side data structure `S'` (may differ)
    unless isStructure env sName && isStructure env sName' do return none
    let sCtor  := getStructureCtor env sName
    let sCtor' := getStructureCtor env sName'
    -- the relation must relate EVERY data field for the specialisation to typecheck; a partial relation (e.g. a
    -- group relating operations but not axioms) skips the constructor — its projections still register.
    unless fieldRels.size == sCtor.numFields && fieldRels.size == sCtor'.numFields do return none
    let sMk  := mkConst sCtor.name  (sCtor.levelParams.map mkLevelParam)   -- `S.mk`  (A-side build)
    let sMk' := mkConst sCtor'.name (sCtor'.levelParams.map mkLevelParam)  -- `S'.mk` (B-side build)
    let «ΘA» := pTy.getAppArgs                                -- each side's data type args
    let «ΘB» := pTy'.getAppArgs
    let k := fieldRels.size
    -- per data field: the two related objects (data projections of `p`/`p'`), their types, and the relation
    -- `Rᵢ` (the field relatedness type with its last two — the related objects — dropped).
    let mut vTys : Array (Expr × Expr) := #[]
    let mut rels : Array Expr := #[]
    for fr in fieldRels do
      let args := (← inferType fr).getAppArgs
      if args.size < 2 then return none
      vTys := vTys.push (← inferType args[args.size - 2]!, ← inferType args[args.size - 1]!)
      rels := rels.push (mkAppN (← inferType fr).getAppFn (args.extract 0 (args.size - 2)))
    -- binders `[v₀ v₀' … , vR₀ …]`: values first (so all are in scope for the `vRᵢ` types and the `S.mk`
    -- applications), relatednesses after; reordered into triples for the lambda.
    let mut decls : Array (Name × (Array Expr → MetaM Expr)) := #[]
    for i in [0 : k] do
      decls := decls.push (s!"v{i}".toName, fun _ => pure vTys[i]!.1)
      decls := decls.push (s!"v{i}'".toName, fun _ => pure vTys[i]!.2)
    for i in [0 : k] do
      decls := decls.push (s!"vR{i}".toName, fun xs => pure (mkApp2 rels[i]! xs[2 * i]! xs[2 * i + 1]!))
    withLocalDeclsD decls fun xs => do
      let sVal  := mkAppN sMk  («ΘA» ++ (Array.range k).map (xs[2 * ·]!))
      let s'Val := mkAppN sMk' («ΘB» ++ (Array.range k).map (xs[2 * · + 1]!))
      let vRs   := (Array.range k).map (fun i => xs[2 * k + i]!)
      let body  := mkAppN srMk (theme ++ #[sVal, s'Val] ++ vRs)
      let mut triples : Array Expr := #[]
      for i in [0 : k] do
        triples := (triples.push xs[2 * i]!).push xs[2 * i + 1]! |>.push xs[2 * k + i]!
      let reordered := theme ++ triples
      let primName := sCtor.name.str "trocqPrim"
      addAndCompile <| .defnDecl {
        name        := primName
        levelParams := lvls
        type        := ← mkForallFVars reordered (← inferType body)
        value       := ← mkLambdaFVars reordered body
        hints       := .abbrev
        safety      := .safe }
      return some primName

/- ===================== (2) STORE: the `@[trocq]` attribute + environment extension =====================
   Tagging `w` classifies it immediately and stores the `RegKind`, rejecting a malformed witness at the tag site. -/

/-- the classified `@[trocq]` witnesses (bases / relators / term primitives). -/
initialize trocqExt : SimplePersistentEnvExtension RegKind (Array RegKind) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := Array.push
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

/-- for a tagged inductive/structure type former, derive + register a `.term` primitive for each of its parts,
    so the user need not hand-write one:
      • a STRUCTURE relation → each FIELD PROJECTION `SR.fieldᵢ` PLUS `S.mk` (via `deriveStructureCtorPrim`);
      • a plain INDUCTIVE relation → each CONSTRUCTOR (via `deriveConstructorPrim`).
    A `def`-based type former (`QuotRel`/`ArrayR`) is neither, so this is a no-op and the user registers by hand. -/
def deriveRelationPrims (indName : Name) : MetaM Unit := do
  let .inductInfo _ ← getConstInfo indName | return
  if isStructure (← getEnv) indName then
    -- a structure relation's field `SR.fieldᵢ` is ALREADY in triple form `(Θ) (s s' self)`, concluding
    -- `Rᵢ (S.projᵢ s) (S'.projᵢ s')`, so `parseEntry` reads it as the primitive for `S.projᵢ` with no reordering.
    -- A field that doesn't classify (e.g. a trivial `PLift True` relatedness) is skipped.
    for fieldName in getStructureFields (← getEnv) indName do
      try modifyEnv (trocqExt.addEntry · (← parseEntry (indName ++ fieldName)))
      catch _ => pure ()
    if let some primName ← deriveStructureCtorPrim indName then
      modifyEnv (trocqExt.addEntry · (← parseEntry primName))
  else
    let .inductInfo ind ← getConstInfo indName | return
    for ctor in ind.ctors do
      if let some primName ← deriveConstructorPrim ctor then
        modifyEnv (trocqExt.addEntry · (← parseEntry primName))

initialize registerBuiltinAttribute {
  name  := `trocq
  descr := "register a LeTrocq relatedness witness (base equivalence / relator / term primitive)"
  add   := fun decl _stx _kind => do
    let entry ← (parseEntry decl).run'
    modifyEnv (trocqExt.addEntry · entry)
    -- a TYPE FORMER also auto-registers its constructors / field projections as term primitives.
    match entry with
    | .typeFormer .. | .groundFormer .. => (deriveRelationPrims decl).run'
    | _ => pure ()
}

/-- the classified witnesses registered in the given environment. -/
def trocqEntries (env : Environment) : Array RegKind := trocqExt.getState env

/- ===================== (3) LOOK UP: registry reads + relator argument-routing =====================
   The pure lookups the graded translation reads (grading itself is inline in `Transfer.assemble`):
   `buildAtomPairs` (type atoms from BASEs), `buildConsts` (relators), `relatorArgKinds` (a relator's
   per-argument routing). -/
open MapClass

/- ===================== per-argument kind of a relator ===================== -/
/-- per-argument kind of a relator, read from its type grouped into triples `(a, a', aRel)` by the SHAPE of `aRel`:
      • `.type (m,n)`          — `aRel : Param m n A A'`;
      • `.family (m,n) domIdx` — `aRel : ∀ …, Param m n (B a)(B' a')` (a dependent type FAMILY, e.g. `Sigma`'s
                                 `β`); `domIdx` indexes the TYPE arg that is the family's domain `A`, read off
                                 `B`'s binder type so the family need NOT sit right after its domain;
      • `.term`                — `aRel` a bare relation. -/
inductive ArgKind
  | type   (cls : ParamClass)
  | family (cls : ParamClass) (domIdx : Nat)
  | term
  deriving Inhabited

/-- read a relator's per-argument routing off its type (see `ArgKind`), so `Transfer.assemble`'s `app` rule
    knows to build each argument's `Param` (TYPE / FAMILY) or send it to the term half (TERM). -/
def relatorArgKinds (wit : Expr) : MetaM (Array ArgKind) := do
  forallTelescopeReducing (← inferType wit) fun bs _ => do
    let triples ← chunkTriples "relator" wit bs
    let mut kinds : Array ArgKind := #[]
    let mut lastTypeIdx : Nat := 0
    for j in [0 : triples.size] do
      let (aBinder, _, aRel) := triples[j]!                 -- `(a, a', aRel)`: the A-binder and the relatedness
      let relTy ← inferType aRel
      if relTy.getAppFn.isConstOf ``Param then
        let a := relTy.getAppArgs
        -- `whnf` the class args: for a graded relator specialized to a demand they are `variance dem`
        -- projections (`(listVariance (map1,map0)).1`), reducing to literal `MapClass`es here.
        kinds := kinds.push (.type (← exprToMapClass (← whnf a[0]!), ← exprToMapClass (← whnf a[1]!)))
        lastTypeIdx := j
      else
        -- a FAMILY arg's relatedness telescopes to a `Param`; anything else is a bare-relation TERM arg.
        let fam? ← forallTelescopeReducing relTy fun _ concl => do
          if concl.getAppFn.isConstOf ``Param then
            let a := concl.getAppArgs
            return some (← exprToMapClass (← whnf a[0]!), ← exprToMapClass (← whnf a[1]!))
          else return none
        match fam? with
        | some cls =>
            -- the family binder `B : A → _` names its domain `A`; find the TYPE-arg triple whose A-binder IS
            -- that `A`, falling back to the most recent type arg if `A` isn't a bare earlier binder.
            let domA := (← whnf (← inferType aBinder)).bindingDomain!
            let mut domIdx := lastTypeIdx
            for k in [0 : j] do
              if triples[k]!.1 == domA then domIdx := k
            kinds := kinds.push (.family cls domIdx)
        | none => kinds := kinds.push .term
    return kinds

/- ===================== registries from the `@[trocq]` extension ===================== -/
/-- type-atom registry from every BASE, BOTH directions (base + `Param.sym`), PAIR-INDEXED
    `srcHead ↦ tgtHead ↦ (tgtTy, wit, cls)` plus the PREFERRED (last-registered) target per source head. -/
def buildAtomPairs : MetaM (NameMap (NameMap (Expr × Expr × ParamClass)) × NameMap Name) := do
  let mut m : NameMap (NameMap (Expr × Expr × ParamClass)) := mkNameMap _
  let mut pref : NameMap Name := mkNameMap _
  for e in trocqEntries (← getEnv) do
    if let .base hA hB tyA tyB witName cls := e then
      let wit ← mkConstWithFreshMVarLevels witName
      let r ← insertBidirPair m pref hA (some hB) (tyB, wit, cls)
        (return (tyA, ← mkAppM ``Param.sym #[wit], (cls.2, cls.1)))
      m := r.1; pref := r.2
  return (m, pref)

/-- the REVERSE of a graded relator `w : ∀ (m n) …triples…, Param m n (P …) (P' …)`:
    `fun m n <each value-pair swapped> => Param.sym (w n m <triples>)`. Swaps `(m n)` (so `Param.sym` lands
    back at `Param m n`) and each `(a, a')`; the relatedness `aRel` stays put — defeq to the reverse's swapped
    slot (the relator analogue of `symPrimitive`). Valid for HETEROGENEOUS predicate relators (all-term args);
    a `Param`-valued TYPE arg would need its relatedness `Param.sym`'d, but no such relator exists (every
    parameterized former is homogeneous `F ↦ F`, needing no reverse). -/
def symRelator (wit : Expr) : MetaM Expr := do
  forallTelescope (← inferType wit) fun bs _ => do
    unless bs.size ≥ 2 do throwError "trocq: relator {wit} lacks the leading `(m n)` binders"
    let m := bs[0]!; let n := bs[1]!
    let triples ← chunkTriples "relator" wit (bs.extract 2 bs.size)
    let mut lamBinders : Array Expr := #[m, n]              -- reverse binders: m, n, then (a', a, aRel)
    let mut appArgs    : Array Expr := #[n, m]              -- call `w` with (n, m) then (a, a', aRel)
    for (a, a', aRel) in triples do
      lamBinders := lamBinders.push a' |>.push a |>.push aRel
      appArgs    := appArgs.push a |>.push a' |>.push aRel
    mkLambdaFVars lamBinders (← mkAppM ``Param.sym #[mkAppN wit appArgs])

/-- constant registry from every RELATOR. FORWARD: keyed by the A-side head. REVERSE: a HETEROGENEOUS relator
    (`P ≠ P'`) ALSO registers under `P'` via `symRelator` (unless a forward relator already claims that head);
    a homogeneous relator (`And ↦ And`) needs no reverse. Every relator is GRADED (specialized to the demand). -/
def buildConsts : MetaM (NameMap Expr) := do
  let mut m := mkNameMap _
  for e in trocqEntries (← getEnv) do
    if let .relator hA _hB witName := e then m := m.insert hA (← mkConstWithFreshMVarLevels witName)
  for e in trocqEntries (← getEnv) do
    if let .relator hA (some hB) witName := e then
      if hB != hA && !m.contains hB then
        m := m.insert hB (← symRelator (← mkConstWithFreshMVarLevels witName))
  return m

/-- ground-base registry from every GROUND equivalence, BOTH directions, HEAD-INDEXED
    `srcHead ↦ #[(srcTy, tgtTy, wit, cls)]`. NOT a selection map: the leaf rule scans the head's entries and
    matches `srcTy` (and, in check mode, `tgtTy`) by `isDefEq`, keeping the LAST match. -/
def buildGround : MetaM (NameMap (Array (Expr × Expr × Expr × ParamClass))) := do
  let mut m : NameMap (Array (Expr × Expr × Expr × ParamClass)) := mkNameMap _
  for e in trocqEntries (← getEnv) do
    if let .ground hA hB tyA tyB witName cls := e then
      let wit ← mkConstWithFreshMVarLevels witName
      let witSym ← mkAppM ``Param.sym #[wit]
      m := m.insert hA ((NameMap.find? m hA |>.getD #[]).push (tyA, tyB, wit, cls))
      m := m.insert hB ((NameMap.find? m hB |>.getD #[]).push (tyB, tyA, witSym, (cls.2, cls.1)))
  return m

end LeTrocq
