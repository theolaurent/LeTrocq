/-
The NATIVE parametricity translation `⟦·⟧`.

Unlike the `Solver` (which builds a graded `Param` *witness* for a TYPE), this is the term-level
abstraction theorem: for any term `t : T` it produces BOTH
  • the native counterpart `t' : T'` (rebuilt over `B` leaf-by-leaf — NOT `iso ∘ t ∘ iso⁻¹`), and
  • the relatedness `tR : ⟦T⟧ t t'`.
It recurses structurally (`.lam`, `.app`, `∀`, sort), bottoms out at registered PRIMITIVES, and unfolds
any other constant's definition. A **type-valued term** (a recursor's motive `M : Nat → Sort`, or any type
family) is routed through the type-level translation — this is how RECURSORS transport: a recursor is a
registered primitive (`Nat.rec ↦ Unary.rec`) whose motive argument is itself translated. `translate% e`
elaborates to the native term `t'`.

`⟦·⟧` is mutually defined on terms (`param`) and types (`paramType`, which returns the relation `R_T`):
  ⟦c⟧        = registered witness, else ⟦unfold c⟧
  ⟦f a⟧      = (f' a', fR a a' aR)                      -- abstraction theorem
  ⟦fun x=>b⟧ = (fun x'=>b', fun x x' xR => bR)
  ⟦A → B⟧    = (A'→B', RArrow R_A R_B)                  -- as a TYPE: returns the relation
-/
import Trocq.Core
import Trocq.Attr
import Lean
open Lean Lean.Meta
namespace Trocq.Translate

/-- registration: type primitives ↦ (B-type, relation `A→B→Type`); term primitives ↦ (B-term, relatedness);
    PROP primitives (predicates) ↦ (B-predicate, equivalence combinator `… → PLift (p a ↔ p' a')`).

    `buildCarrier` is the SOLVER's witness builder, INJECTED as data (not imported): `param`'s `Quot.lift`
    case calls it to obtain the `Param` (hence the MAPS) of an ARBITRARY carrier — not just a registered base.
    `Translate` does not depend on `Solver`; the caller (`Trocq.Solver`/the surface elaborators) supplies
    `fun ty => (transfer ty (4,4)).1` here. This is how the genuine `Translate`↔`Solver` mutual recursion is
    expressed WITHOUT a global mutable hook — see `AGENTS.md`. -/
structure Ctx where
  types : NameMap (Expr × Expr)
  terms : NameMap (Expr × Expr)
  props : NameMap (Expr × Expr)
  buildCarrier : Expr → MetaM Expr

/-- bound-variable environment: `fvar ↦ (x', xR, paramOpt)`. `xR` is the relatedness (for a type var, its
    relation). `paramOpt` is the bound type variable's full `Param` (with MAPS), threaded so eliminators like
    `Quot.lift` over a type-VARIABLE carrier can use its maps; `none` for term/base binders. -/
abbrev Env := List (FVarId × Expr × Expr × Option Expr)

/-- recognize a numeral — a raw `.lit (.natVal n)` or an `@OfNat.ofNat _ (lit n) _` — as `n`. The caller
    must additionally check the expression's type is `Nat` (the type argument here may be unreduced). -/
def natNumeral? (e : Expr) : Option Nat :=
  if let some n := e.rawNatLit? then some n
  else if e.getAppFn.isConstOf ``OfNat.ofNat then
    let args := e.getAppArgs
    if args.size == 3 then args[1]!.rawNatLit? else none
  else none

/-- assign every residual (unconstrained) universe mvar in `e` (and its type) to `0` — used in the `Quot.lift`
    case to put translate's relations and the solver-built carrier `Param`s at the SAME (level-0) universes
    before combining them (the relations live in `Type 0`; only the carrier's own level may be higher, and
    that is carried by the result term, not these relations). -/
def zeroResidualLevels (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let st := Lean.collectLevelMVars (Lean.collectLevelMVars {} e) (← instantiateMVars (← inferType e))
  for mid in st.result do
    unless (← isLevelMVarAssigned mid) do assignLevelMVar mid levelZero
  instantiateMVars e

/-- expand `n` to its `Nat.succ`/`Nat.zero` normal form, so a numeral leaf reduces to registered primitives. -/
def natExpr : Nat → Expr
  | 0 => mkConst ``Nat.zero
  | n + 1 => mkApp (mkConst ``Nat.succ) (natExpr n)

/- ===================== kernel primitives (built-in, NOT `@[trocq]`-registered) =====================
   The single table of constants the translation knows intrinsically: each maps a head to its `(counterpart,
   relation/relatedness)`, given the occurrence's universe levels. The level policy is PER-PRIMITIVE, which is
   why this is a table of functions rather than plain entries: `Quot`'s relation `QuotRel` has its own (fixed)
   universes pinned later by its arguments, so it takes FRESH level mvars; `PUnit`'s relation is the trivial,
   level-UNconstrained `UnitRel`, so its counterpart/relatedness must reuse the OCCURRENCE's levels (nothing
   else pins them). Their relations live in `Core/Quot` and `Core/Unit`. Adding a primitive is one entry here
   (plus its `Param` relator in `Solver.buildConsts` if it can also appear as a goal TYPE, as `Quot` does).
   `Quot.lift` is NOT here — an eliminator is a synthesis procedure, not a relation; see `param`'s special case. -/
def typePrimitives : List (Name × (List Level → MetaM (Expr × Expr))) :=
  [ (``PUnit, fun lvls => return (.const ``PUnit lvls, .const ``UnitRel lvls)),
    (``Quot,  fun _    => return (← mkConstWithFreshMVarLevels ``Quot, ← mkConstWithFreshMVarLevels ``QuotRel)) ]

def termPrimitives : List (Name × (List Level → MetaM (Expr × Expr))) :=
  [ (``PUnit.unit, fun lvls => return (.const ``PUnit.unit lvls, .const ``UnitR lvls)),
    (``Quot.mk,    fun _    => return (← mkConstWithFreshMVarLevels ``Quot.mk, ← mkConstWithFreshMVarLevels ``QuotMkR)) ]

mutual
/-- translate a TYPE `A` to `(A', R_A)` where `R_A : A → A' → Type` is the parametricity relation. -/
partial def paramType (ctx : Ctx) (env : Env) : Expr → MetaM (Expr × Expr)
  | .const c lvls => do
      -- a kernel primitive (`PUnit`/`Quot`), else a registered former, else unfold the definition.
      if let some mk := typePrimitives.lookup c then return ← mk lvls
      match ctx.types.find? c with
      | some p => return p
      | none =>
          let some val := (← getConstInfo c).value? | throwError "paramType: opaque/unregistered type {c}"
          paramType ctx env (val.instantiateLevelParams (← getConstInfo c).levelParams lvls)
  | .fvar id => do
      match env.find? (·.1 == id) with
      | some (_, A', relA, _) => return (A', relA)
      | none => throwError "paramType: unbound type variable"
  | .app f a => do
      let (f', fR) ← paramType ctx env f
      let (a', aR) ← param ctx env a
      return (.app f' a', mkApp3 fR a a' aR)
  | .sort lvl => do
      -- ⟦Sort u⟧: the B-side is the same sort. The relation between two TYPES is "a relation"
      -- `R_{Type} A A' := A → A' → Type`; the relation between two PROPS is logical equivalence
      -- `R_{Prop} P P' := PLift (P ↔ P')` (matching `paramProp`/the Prop universe), so a `Prop`-valued
      -- component relates by `↔`, not the generic proof-relevant `→ Type`.
      match ← instantiateLevelMVars lvl with
      | .zero =>
          let rel ← withLocalDeclD `P (.sort .zero) fun P => withLocalDeclD `P' (.sort .zero) fun P' => do
            mkLambdaFVars #[P, P'] (← mkAppM ``PLift #[← mkAppM ``Iff #[P, P']])
          return (.sort .zero, rel)
      | lvl =>
          let rel ← withLocalDeclD `A (.sort lvl) fun A => withLocalDeclD `B (.sort lvl) fun B => do
            mkLambdaFVars #[A, B] (← mkArrow A (← mkArrow B (.sort 1)))
          return (.sort lvl, rel)
  | e@(.forallE n A B _) => do
      -- ONE construction for arrow AND dependent Π: R_{∀x,B} f g := ∀ x x' (xR : R_A x x'), R_{B x} (f x)(g x')
      -- (built explicitly, NOT via `RArrow`, so the domain and codomain relations may live at DIFFERENT
      -- universes — needed when the codomain is a `Sort`, e.g. a recursor/matcher motive `Nat → Sort`).
      let (A', relA) ← paramType ctx env A
      withLocalDeclD n A fun x =>
      withLocalDeclD (n.appendAfter "'") A' fun x' =>
      withLocalDeclD (n.appendAfter "R") (mkApp2 relA x x') fun xR => do
        let (Bx', relBx) ← paramType ctx ((x.fvarId!, x', xR, none) :: env) (B.instantiate1 x)
        let T' ← mkForallFVars #[x'] Bx'
        let rel ← withLocalDeclD `f e fun f => withLocalDeclD `g T' fun g => do
          let body ← mkForallFVars #[x, x', xR] (mkApp2 relBx (.app f x) (.app g x'))
          mkLambdaFVars #[f, g] body
        return (T', rel)
  | e => throwError "paramType: unsupported type {e}"

/-- translate a TERM `t : T` to `(t', tR)` where `tR : R_T t t'`. -/
partial def param (ctx : Ctx) (env : Env) (e : Expr) : MetaM (Expr × Expr) := do
  let ty ← inferType e
  -- a PROPOSITION (`e : Prop`) relates by logical equivalence, via `paramProp`; a (larger) TYPE-valued term
  -- relates by the parametricity *relation*, via `paramType` (this is what lets a recursor's motive
  -- `M : Nat → Sort` or any type-family argument translate). The two meet here.
  if let .sort lvl := ty then
    if (← instantiateLevelMVars lvl) == levelZero then return ← paramProp ctx env e
    else return ← paramType ctx env e
  -- a `Nat` numeral leaf (raw `.lit` or `OfNat.ofNat …`, possibly at an unreduced type like `motive 0`):
  -- expand to its `succ`/`zero` normal form and translate through the registered primitives.
  if let some n := natNumeral? e then
    if (← whnf ty).isConstOf ``Nat then return ← param ctx env (natExpr n)
  -- `Quot.lift f h [q]`: special-cased because the respect proof `h` cannot be translated structurally (it is
  -- a `∀`-eq proof, and `Eq`/`*.elim` are not registered). We translate `f`/`q`, SYNTHESISE `h'` from the
  -- carriers' equivalence MAPS (`quotLiftResp`), and build the relatedness via the eliminator's parametricity
  -- (`quotLiftRel`).
  --
  -- ⚠ TYPE-VARIABLE carrier — `relate%` works, `translate%` does NOT, and this is a SEMANTIC wall (not a gap):
  --   The synthesised `h'` uses the carrier's `Param` `pA` (its maps). For a CONCRETE carrier `pA` is closed
  --   (built by the solver), so both the counterpart `Quot.lift f' h'` and the relatedness are closed — both
  --   surfaces work. For a TYPE-VARIABLE carrier `pA` is the bound type's env `Param`, i.e. a *relatedness*
  --   binder: it is in scope in `relate%`'s output (which binds `A A' pA`), but NOT in the pure B-side
  --   counterpart (which binds only `A'`). So `relate%` succeeds, while `translate%` would leave `pA` free.
  --   That is fundamental: a quotient lift's respect proof needs the `A ≃ A'` maps, which are relatedness
  --   data — there is no pure B-side `h'` to rebuild (even when one exists abstractly, e.g. `r' = False`, the
  --   maps-free proof `fun _ _ h => h.elim` is unreachable because translating it hits `Eq`/`False.elim`).
  if e.getAppFn.isConstOf ``Quot.lift then
    let args := e.getAppArgs
    if args.size == 5 || args.size == 6 then
      let A := args[0]!; let r := args[1]!; let B := args[2]!; let f := args[3]!; let hresp := args[4]!
      let (A', αR) ← paramType ctx env A
      let (r', rR) ← param ctx env r
      let (f', fR) ← param ctx env f
      -- translate's relations carry fresh universe mvars; the solver builds the carriers' `Param`s (hence
      -- MAPS) at concrete level 0 for ANY carrier. Zero translate's residual levels too so they agree.
      let (αR, rR, fR) := (← zeroResidualLevels αR, ← zeroResidualLevels rR, ← zeroResidualLevels fR)
      -- the carrier's `Param` (its MAPS): a type-VARIABLE carrier reads it from the `env` (threaded by the
      -- type-binder case of `.lam`); a concrete carrier has the solver build it on demand. For a type var the
      -- result `pT` is a relatedness binder — see the ⚠ note above: `h'` then refers to it, which is fine for
      -- the relatedness but makes the counterpart open (so `translate%` of a polymorphic lift is impossible).
      let carrierParam (T : Expr) : MetaM Expr := do
        match T with
        | .fvar id => match (env.find? (·.1 == id)).bind (·.2.2.2) with
                      | some pT => pure pT
                      | none => ctx.buildCarrier T
        | _ => ctx.buildCarrier T
      let pa ← carrierParam A
      let pb ← carrierParam B
      let h' ← mkAppM ``Trocq.quotLiftResp #[pa, pb, rR, fR, hresp]
      let fn ← mkAppM ``Quot.lift #[f', h']   -- α'/r'/β' inferred from `f'`/`h'` (unifies the levels)
      if args.size == 6 then
        let (q', qR) ← param ctx env args[5]!
        return (mkApp fn q', ← mkAppM ``Trocq.quotLiftRel #[pa, pb, rR, fR, hresp, h', args[5]!, q', qR])
      else
        -- the function `Quot.lift f h : Quot r → β`: relatedness is `fun q q' qR => quotLiftRel … q q' qR`.
        let quotRel ← mkAppM ``Trocq.QuotRel #[A, A', αR, r, r', rR]
        let quotR ← mkAppM ``Quot #[r]
        let quotR' ← mkAppM ``Quot #[r']
        let rel ← withLocalDeclD `q quotR fun q =>
          withLocalDeclD `q' quotR' fun q' =>
            withLocalDeclD `qR (mkApp2 quotRel q q') fun qR => do
              mkLambdaFVars #[q, q', qR]
                (← mkAppM ``Trocq.quotLiftRel #[pa, pb, rR, fR, hresp, h', q, q', qR])
        return (fn, rel)
  match e with
  | .fvar id => do
      match env.find? (·.1 == id) with
      | some (_, x', xR, _) => return (x', xR)
      | none => throwError "param: unbound variable"
  | .const c lvls => do
      -- a kernel primitive (`PUnit.unit`/`Quot.mk`), else a registered term primitive, else unfold the
      -- definition. (`Quot.lift`, an ELIMINATOR, is handled by the special case above, not the table.)
      if let some mk := termPrimitives.lookup c then return ← mk lvls
      match ctx.terms.find? c with
      | some p => return p
      | none =>
          let some val := (← getConstInfo c).value? | throwError "param: opaque/unregistered constant {c}"
          param ctx env (val.instantiateLevelParams (← getConstInfo c).levelParams lvls)
  | .app f a => do
      let (f', fR) ← param ctx env f
      let (a', aR) ← param ctx env a
      return (.app f' a', mkApp3 fR a a' aR)
  | .lam n A b _ => do
      let (A', relA) ← paramType ctx env A
      withLocalDeclD n A fun x =>
      withLocalDeclD (n.appendAfter "'") A' fun x' => do
        -- a TYPE binder (`A : Sort _`) binds a full `Param` (top class) and threads it into the `env`, so the
        -- body has the bound type's MAPS — e.g. for a `Quot.lift` over a type-VARIABLE carrier (see the ⚠ note
        -- in the `Quot.lift` case). Note this `Param` `pA` is a RELATEDNESS binder: it appears in the `relate%`
        -- output but not in the `translate%` counterpart (which binds only `x'`). A term/base binder binds the
        -- bare relatedness `relA x x'`.
        if A.isSort then
          -- `@Param.{u,0} map4 map4 x x'` with `u` the binder's sort level (the relation lands in `Type 0`).
          let pTy := mkApp4 (.const ``Param [A.sortLevel!, levelZero])
            (mkConst ``MapClass.map4) (mkConst ``MapClass.map4) x x'
          withLocalDeclD (n.appendAfter "R") pTy fun pA => do
            let (b', bR) ← param ctx ((x.fvarId!, x', ← mkAppM ``Param.R #[pA], some pA) :: env) (b.instantiate1 x)
            return (← mkLambdaFVars #[x'] b', ← mkLambdaFVars #[x, x', pA] bR)
        else
          withLocalDeclD (n.appendAfter "R") (mkApp2 relA x x') fun xR => do
            let (b', bR) ← param ctx ((x.fvarId!, x', xR, none) :: env) (b.instantiate1 x)
            return (← mkLambdaFVars #[x'] b', ← mkLambdaFVars #[x, x', xR] bR)
  | e => throwError "param: unsupported term {e}"

/-- translate a PROPOSITION `P` to `(P', h)` where `h : PLift (P ↔ P')` — its logical-equivalence relatedness.
    Unlike `∀`-transport (which needs the domain's backward map and so belongs to the solver), an equivalence
    is built from the *relations* alone: logical connectives combine their parts' equivalences congruently, and
    a registered predicate supplies its own (the abstraction theorem `⟦p a₁…⟧ = pR a₁ a₁' a₁R …`). -/
partial def paramProp (ctx : Ctx) (env : Env) (P : Expr) : MetaM (Expr × Expr) := do
  let args := P.getAppArgs
  match P.getAppFn with
  | .const c _ =>
      if (c == ``True || c == ``False) && args.isEmpty then
        return (P, ← mkAppM ``PLift.up #[← mkAppOptM ``Iff.rfl #[P]])
      else if c == ``Not && args.size == 1 then
        let (Q', hQ) ← paramProp ctx env args[0]!
        return (← mkAppM ``Not #[Q'],
          ← mkAppM ``PLift.up #[← mkAppM ``not_congr #[← mkAppM ``PLift.down #[hQ]]])
      else if (c == ``And || c == ``Or || c == ``Iff) && args.size == 2 then
        let (L', hL) ← paramProp ctx env args[0]!
        let (R', hR) ← paramProp ctx env args[1]!
        let cong := if c == ``And then ``and_congr else if c == ``Or then ``or_congr else ``iff_congr
        return (mkApp2 (.const c []) L' R',
          ← mkAppM ``PLift.up #[← mkAppM cong #[← mkAppM ``PLift.down #[hL], ← mkAppM ``PLift.down #[hR]]])
      else match ctx.props.find? c with
        | some (head', wit) =>
            -- the abstraction theorem for a registered predicate `p`: `⟦p a₁ … aₙ⟧ = pR a₁ a₁' a₁R …`.
            let mut cnt := head'
            let mut rel := wit
            for a in args do
              let (a', aR) ← param ctx env a
              cnt := .app cnt a'
              rel := mkApp3 rel a a' aR
            return (cnt, rel)
        | none => throwError "paramProp: unregistered/opaque proposition head {c}"
  | f => throwError "paramProp: unsupported proposition (head {f})"
end

/-- telescope a primitive's type into abstraction-theorem triples `[a,a',aR, b,b',bR, …]`, check the binder
    count is a multiple of 3, and run `k` with the binders `xs` and their VALUE-SWAPPED reordering
    `[a',a,aR, b',b,bR, …]` (the relatedness slot stays put). The shared frame of the backward builders. -/
def withSwappedTriples (what : String) (wit : Expr) (k : Array Expr → Array Expr → MetaM Expr) :
    MetaM Expr := do
  forallTelescope (← inferType wit) fun xs _ => do
    unless xs.size % 3 == 0 do
      throwError "trocq: {what} is not in abstraction-theorem triple form ({xs.size} binders): {wit}"
    let mut swapped : Array Expr := #[]
    for j in [0 : xs.size / 3] do
      swapped := (swapped.push xs[3*j+1]!).push xs[3*j]! |>.push xs[3*j+2]!
    k xs swapped

/-- swap the (A-value, B-value) in each abstraction-theorem triple of a term primitive, giving the
    BACKWARD-direction combinator. A primitive is `cWit : ∀ a a' (aR : R a a') …, R (c …) (c' …)`
    (binders in triples); this returns `fun a' a aR … => cWit a a' aR …`. Its relatedness binder keeps the
    type `R a a'`, which is *defeq* to the symmetric relation `R.sym a' a` the backward direction supplies —
    so the same proof term serves both directions, only the value arguments swap position. -/
def symPrimitive (wit : Expr) : MetaM Expr :=
  withSwappedTriples "term primitive" wit fun xs swapped => mkLambdaFVars swapped (mkAppN wit xs)

/-- the backward direction of a PROP primitive `pR : ∀ triples, PLift (p … ↔ p' …)`: like `symPrimitive`
    (swap each triple's value pair), but the conclusion is an `Iff`, so the proof is `Iff.symm`'d too. -/
def symProp (wit : Expr) : MetaM Expr :=
  withSwappedTriples "prop primitive" wit fun xs swapped => do
    let pf ← mkAppM ``PLift.up #[← mkAppM ``Iff.symm #[← mkAppM ``PLift.down #[mkAppN wit xs]]]
    mkLambdaFVars swapped pf

/-- the translation context assembled from the `@[trocq]` extension, in BOTH directions: every BASE gives a
    type relation forward (`Param.R`) and backward (`Param.R ∘ Param.sym`); every TERM primitive gives its
    `c ↦ c'` map + relatedness forward, and the swapped `c' ↦ c` map + `symPrimitive` relatedness backward.
    So a term over *either* side of a registered equivalence translates by head match. The caller injects
    `buildCarrier` (the solver's witness builder) — see `Ctx`. -/
def buildCtx (buildCarrier : Expr → MetaM Expr) : MetaM Ctx := do
  let mut types := mkNameMap _
  let mut terms := mkNameMap _
  let mut props := mkNameMap _
  -- every BASE / TERM / PROP primitive installs in both directions via `insertBidir` (the shared
  -- forward/backward + homogeneous-skip policy); the backward witness is the relevant `sym*`.
  for e in trocqEntries (← getEnv) do
    match e with
    | .base hA hB tyA tyB witName _ =>
        let wit ← mkConstWithFreshMVarLevels witName
        types ← insertBidir types hA (some hB) (tyB, ← mkAppM ``Param.R #[wit])
          (return (tyA, ← mkAppM ``Param.R #[← mkAppM ``Param.sym #[wit]]))
    | .term hA bTerm witName =>
        -- the backward key is the B-side head (so a homogeneous constructor like `List.cons` is skipped).
        let wit ← mkConstWithFreshMVarLevels witName
        terms ← insertBidir terms hA bTerm.constName? (bTerm, wit)
          (return (← mkConstWithFreshMVarLevels hA, ← symPrimitive wit))
    | .propPrim hA hB witName =>
        let wit ← mkConstWithFreshMVarLevels witName
        props ← insertBidir props hA (some hB) (← mkConstWithFreshMVarLevels hB, wit)
          (return (← mkConstWithFreshMVarLevels hA, ← symProp wit))
    | .typeFormer hA hB relName =>
        -- a parameterized type former `F`: `paramType` crosses `F a` via `(F', relFormer)`, where
        -- `relFormer a a' aR : F a → F' a' → Type` is applied by the `.app` rule's `mkApp3`. ONE entry
        -- serves BOTH directions (the per-argument relation `aR` carries the direction and `relFormer` is
        -- polymorphic in it), so no `sym` exists to install — forward only.
        types := types.insert hA (← mkConstWithFreshMVarLevels hB, ← mkConstWithFreshMVarLevels relName)
    | .relator .. => pure ()
  return { types, terms, props, buildCarrier }

end Trocq.Translate
