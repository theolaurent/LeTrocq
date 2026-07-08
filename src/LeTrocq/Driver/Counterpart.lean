/-
The TERM TRANSLATION `⟨·⟩` (the counterpart translation).

For a term/type `e` it produces the B-side counterpart `⟨e⟩` — `e` rebuilt leaf-by-leaf over `B` (NOT
`iso ∘ e ∘ iso⁻¹`), bottoming at registered PRIMITIVES; an unregistered head is an ERROR (never unfolds).

  ⟨c⟩        = registered counterpart (term primitive / type former / Prop predicate; else error)
  ⟨x⟩        = x'                                       (bound variable's counterpart)
  ⟨f a⟩      = ⟨f⟩ ⟨a⟩
  ⟨fun x=>b⟩ = fun x'=>⟨b⟩
  ⟨Πx:A. B⟩  = Πx':⟨A⟩. ⟨B⟩

The other half is the RELATEDNESS `[e] : 〚T〛 e ⟨e⟩`, the graded `[·]` in `LeTrocq.Driver.Transfer` (the sole
consumer of `⟨·⟩`). `translate e` elaborates to `⟨e⟩`; the shared `Ctx`/`buildCtx`/`sym*` below serve both.
-/
import LeTrocq.Combinators
import LeTrocq.Driver.Registry
import Lean
open Lean Lean.Meta
namespace LeTrocq.Counterpart

/-- lookup direction for `⟨·⟩`: `fwd` prefers a head's registered TARGET (`A ↦ B`), `bwd` its registered
    SOURCE (`B ↦ A`). Only affects SYNTH-mode leaf selection where a head is registered in BOTH roles; each
    direction falls back to the other, so a single-role head still resolves. `transfer from` runs `fwd`;
    `transfer to` runs `bwd` to synthesize the SOURCE of the named target. -/
inductive Direction | fwd | bwd
  deriving DecidableEq, Inhabited

/-- a per-head preferred counterpart, split by registration direction; `get dir` prioritizes `dir`'s map
    and falls back to the other (so a head registered in only one role still resolves). -/
structure DirPref where
  fwd : NameMap Name
  bwd : NameMap Name

def DirPref.get (p : DirPref) : Direction → Name → Option Name
  | .fwd, c => (p.fwd.find? c).orElse fun _ => p.bwd.find? c
  | .bwd, c => (p.bwd.find? c).orElse fun _ => p.fwd.find? c

/-- the `⟨·⟩` registration (COUNTERPARTS only): type formers/bases/relators ↦ B-side head; term primitives ↦
    (B-term, relatedness witness). The second component of `terms` (the relatedness) is what `[·]` reads; `⟨·⟩`
    uses only the first. A `Prop`'s counterpart comes from its RELATOR entry in `types` (`And ↦ And`,
    `Pos ↦ Pos'`); its relatedness is the graded `Param` witness `[·]` builds. -/
structure Ctx where
  types    : NameMap (NameMap Expr)
  typePref : DirPref
  terms    : NameMap (NameMap (Expr × Expr))
  termPref : DirPref
  -- GROUND closed-type equivalences (`List Unit ↦ Nat`), HEAD-INDEXED `srcHead ↦ #[(srcTy, tgtTy, dir)]`,
  -- matched WHOLE by `isDefEq` (the counterpart side only — `⟨·⟩` needs just the target TYPE). Each entry
  -- carries its registration `Direction`, so synth prefers the requested direction's entries.
  ground   : NameMap (Array (Expr × Expr × Direction))

/-- counterpart environment for `⟨·⟩`: `fvar ↦ x'`, the bound variable's B-side counterpart. (The graded
    translation `[·]` in `LeTrocq.Driver.Transfer` carries the relatedness separately; `⟨·⟩` needs only `x'`.) -/
abbrev TEnv := List (FVarId × Expr)

/-- recognize a numeral — a raw `.lit (.natVal n)` or an `@OfNat.ofNat _ (lit n) _` — as `n`. The caller
    must additionally check the expression's type is `Nat` (the type argument here may be unreduced). -/
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

/-- a sentinel target-key for term primitives whose result type is NOT constant-headed — a recursor, say,
    polymorphic in its motive (`Unary.rec : … → M' m`). Such a primitive is not target-selectable, only
    reachable via the preferred (synth) default, so all its registrations share this one key. -/
def polyResultKey : Name := `_LeTrocq.polyResult

/-- head of a term primitive's RESULT type, telescoping through its arguments — the target-TYPE key a
    term primitive is filed under (`Unary.s : Unary → Unary` ↦ `Unary`, `Nat.zero : Nat` ↦ `Nat`,
    `List.cons : {α} → α → List α → List α` ↦ `List`); a non-constant conclusion ↦ `polyResultKey`. -/
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

/-- `⟨·⟩` — THE TERM TRANSLATION: rebuild `e`'s B-side counterpart leaf by leaf. A
    registered head maps to its counterpart (a term primitive `Nat.succ ↦ Unary.s`, a type former
    `List ↦ List`, or a `Prop` predicate `p ↦ p'`); a bound variable to its counterpart `x'`; a Π/λ/app/sort
    structurally; a `Nat` numeral through its `succ`/`zero` normal form. An unregistered head is an ERROR —
    the translation never unfolds. An optional `tgt?` (the demanded counterpart TYPE) selects registered
    heads TYPE-DIRECTEDLY (e.g. `Nat.zero ↦ Unary.z` at target `Unary`, `↦ Nat.zero` at target `Nat`) and
    is destructured down an application spine (the head's counterpart type dictates each argument's target).
    This produces ONLY the counterpart; the relatedness is the graded `[·]` in `LeTrocq.Driver.Transfer`, which
    calls back here for every counterpart it needs (`[t u] = [t] u ⟨u⟩ [u]`). -/
partial def term (ctx : Ctx) (env : TEnv) (e : Expr) (tgt? : Option Expr) (dir : Direction := .fwd) :
    MetaM Expr := do
  -- GROUND closed-type equivalence (`⟨List Unit⟩ = Nat`): matched WHOLE (head-indexed, `isDefEq`), so it beats
  -- the structural `.app`/`.const` descent below. Only type-EXPRESSIONS match (`srcTy` is a type); a term of the
  -- ground type is never `isDefEq` to that type, so no misfire. Prefers a `dir`-matching entry, else any (each
  -- keeping the LAST match — the last-registered default).
  if let some h := e.getAppFn.constName? then
    if let some cands := NameMap.find? ctx.ground h then
      let mut prefHit : Option Expr := none
      let mut anyHit  : Option Expr := none
      for (srcTy, tgtTy, d) in cands do
        if ← (try isDefEq e srcTy catch _ => pure false) then
          let ok ← match tgt? with
            | some t => (try isDefEq t tgtTy catch _ => pure false)
            | none   => pure true
          if ok then
            anyHit := some tgtTy
            if d == dir then prefHit := some tgtTy
      if let some tgtTy := prefHit.orElse (fun _ => anyHit) then return tgtTy
  if let some n := natNumeral? e then
    if (← whnf (← inferType e)).isConstOf ``Nat then return ← term ctx env (natExpr n) tgt? dir
  match e with
  | .fvar id =>
      match env.find? (·.1 == id) with
      | some (_, x') => return x'
      | none => throwError "translate: unbound variable {e}"
  | .const c _ =>
      -- one registry lookup: term primitives, then type formers/bases, then `Prop` predicates. In CHECK mode
      -- the target head selects the counterpart; in SYNTH mode the preferred (last-registered) target is used.
      let key? := (← whnf (tgt?.getD e)).getAppFn.constName?
      if let some tgtMap := ctx.terms.find? c then
        let some h := (match tgt? with | some _ => key? | none => ctx.termPref.get dir c)
          | throwError "translate: term {c} has no target"
        match tgtMap.find? h with
        | some (b, _) => return b
        | none =>
            -- DIAGONAL target: the demanded counterpart TYPE is the source's own type ⇒ `c` is its own counterpart.
            if (← (tgt?.mapM fun t => do isDefEq (← inferType e) t)).getD false then return e
            else throwError "translate: no counterpart for term {c} at target {h}"
      else if let some tgtMap := ctx.types.find? c then
        let some h := (match tgt? with | some _ => key? | none => ctx.typePref.get dir c)
          | throwError "translate: type {c} has no target"
        match tgtMap.find? h with
        | some b => return b
        | none =>
            if (← (tgt?.mapM fun t => do isDefEq e t)).getD false then return e
            else throwError "translate: no counterpart for type {c} at target {h}"
      else
        -- UNREGISTERED constant ⇒ its own counterpart (the diagonal). Soundness is upstream: the whole-diagonal
        -- short-circuit in `Transfer` only relies on this after verifying the surrounding type/term is diagonal.
        return e
  | e@(.app ..) => do
      match tgt? with
      | none => return .app (← term ctx env e.appFn! none dir) (← term ctx env e.appArg! none dir)
      | some _ =>
          -- SPINE: resolve the head against the result target, then take each argument's target from the
          -- head counterpart's type (its domain), threading dependent codomains via the built counterpart.
          let fn := e.getAppFn
          let mut acc ← term ctx env fn tgt? dir
          let mut ty ← inferType acc
          for a in e.getAppArgs do
            let (dom, cod) ← match (← whnf ty) with
              | .forallE _ d b _ => pure (d, b)
              | other => throwError "translate: head counterpart type {other} is not a function"
            let a' ← term ctx env a (some dom) dir
            acc := .app acc a'; ty := cod.instantiate1 a'
          return acc
  | .sort _ => return e
  | .lam n A b _ => do
      let (domTgt?, bodyTgt?) ← splitPi? tgt?
      let A' ← term ctx env A domTgt? dir
      withLocalDeclD n A fun x => withLocalDeclD (n.appendAfter "'") A' fun x' =>
        return ← mkLambdaFVars #[x'] (← term ctx ((x.fvarId!, x') :: env) (b.instantiate1 x)
          (bodyTgt?.map (·.instantiate1 x')) dir)
  | .forallE n A B _ => do
      let (domTgt?, bodyTgt?) ← splitPi? tgt?
      let A' ← term ctx env A domTgt? dir
      withLocalDeclD n A fun x => withLocalDeclD (n.appendAfter "'") A' fun x' =>
        return ← mkForallFVars #[x'] (← term ctx ((x.fvarId!, x') :: env) (B.instantiate1 x)
          (bodyTgt?.map (·.instantiate1 x')) dir)
  | e => throwError "translate: unsupported {e}"

/-- telescope a primitive's type into abstraction-theorem triples `[a,a',aRel, b,b',bR, …]`, check the binder
    count is a multiple of 3, and run `k` with the binders `xs` and their VALUE-SWAPPED reordering
    `[a',a,aRel, b',b,bR, …]` (the relatedness slot stays put). The shared frame of the backward builders. -/
def withSwappedTriples (what : String) (wit : Expr) (k : Array Expr → Array Expr → MetaM Expr) :
    MetaM Expr := do
  forallTelescope (← inferType wit) fun xs _ => do
    let mut swapped : Array Expr := #[]
    for (a, a', aRel) in ← chunkTriples what wit xs do
      swapped := swapped.push a' |>.push a |>.push aRel     -- swap the value pair, keep the relatedness
    k xs swapped

/-- swap the (A-value, B-value) in each abstraction-theorem triple of a term primitive, giving the
    BACKWARD-direction combinator. A primitive is `cWit : ∀ a a' (aRel : R a a') …, R (c …) (c' …)`
    (binders in triples); this returns `fun a' a aRel … => cWit a a' aRel …`. Its relatedness binder keeps the
    type `R a a'`, which is *defeq* to the symmetric relation `R.sym a' a` the backward direction supplies —
    so the same proof term serves both directions, only the value arguments swap position. -/
def symPrimitive (wit : Expr) : MetaM Expr :=
  withSwappedTriples "term primitive" wit fun xs swapped => mkLambdaFVars swapped (mkAppN wit xs)

/-- the translation context assembled from the `@[trocq]` extension, in BOTH directions: every BASE gives a
    type relation forward (`Param.R`) and backward (`Param.R ∘ Param.sym`); every TERM primitive gives its
    `c ↦ c'` map + relatedness forward, and the swapped `c' ↦ c` map + `symPrimitive` relatedness backward.
    So a term over *either* side of a registered equivalence translates by head match. -/
def buildCtx : MetaM Ctx := do
  let mut types     : NameMap (NameMap Expr) := mkNameMap _
  let mut typePrefF : NameMap Name := mkNameMap _
  let mut typePrefB : NameMap Name := mkNameMap _
  let mut terms     : NameMap (NameMap (Expr × Expr)) := mkNameMap _
  let mut termPrefF : NameMap Name := mkNameMap _
  let mut termPrefB : NameMap Name := mkNameMap _
  let mut ground    : NameMap (Array (Expr × Expr × Direction)) := mkNameMap _
  -- every BASE / TERM installs in both directions (the shared forward/backward + homogeneous-skip policy),
  -- with a per-DIRECTION preferred (last-registered) target; the backward witness is `symPrimitive`.
  for e in trocqEntries (← getEnv) do
    match e with
    | .base hA hB tyA tyB _witName _ =>
        -- `⟨·⟩` needs only the COUNTERPART type, both directions: `⟨A⟩ = B` (fwd), `⟨B⟩ = A` (bwd).
        let r ← insertBidirPair types typePrefF typePrefB hA (some hB) tyB (return tyA)
        types := r.1; typePrefF := r.2.1; typePrefB := r.2.2
    | .ground hA hB tyA tyB _witName _ =>
        -- a GROUND closed-type equivalence: `⟨A⟩ = B` (fwd), `⟨B⟩ = A` (bwd), matched WHOLE (`isDefEq`).
        ground := ground.insert hA ((NameMap.find? ground hA |>.getD #[]).push (tyA, tyB, .fwd))
        ground := ground.insert hB ((NameMap.find? ground hB |>.getD #[]).push (tyB, tyA, .bwd))
    | .term hA bTerm witName =>
        -- forward: source head ↦ counterpart's RESULT-TYPE head ↦ (counterpart, relatedness). The backward
        -- entry is keyed by the B-side term head (so a homogeneous constructor like `List.cons` is skipped).
        let wit ← mkConstWithFreshMVarLevels witName
        let srcTerm ← mkConstWithFreshMVarLevels hA
        let tgtTyHead ← resultTypeHead bTerm
        terms := terms.insert hA ((NameMap.find? terms hA |>.getD (mkNameMap _)).insert tgtTyHead (bTerm, wit))
        termPrefF := termPrefF.insert hA tgtTyHead
        match bTerm.constName? with
        | some hB =>
            if hB != hA then
              let srcTyHead ← resultTypeHead srcTerm
              terms := terms.insert hB ((NameMap.find? terms hB |>.getD (mkNameMap _)).insert srcTyHead
                (srcTerm, ← symPrimitive wit))
              termPrefB := termPrefB.insert hB srcTyHead
        | none => pure ()
    | .typeFormer hA hB _relName =>
        -- a parameterized type former `F`: `⟨·⟩` maps its head `F ↦ F'` (`⟨F a⟩ = F' ⟨a⟩`, via the `.app`
        -- rule). ONE entry, forward only, keyed by the B-side head.
        types := types.insert hA ((NameMap.find? types hA |>.getD (mkNameMap _)).insert hB
          (← mkConstWithFreshMVarLevels hB))
        typePrefF := typePrefF.insert hA hB
    | .relator hA (some hB) _witName =>
        -- a RELATOR ALSO supplies `⟨·⟩` the head counterpart `P ↦ P'` (read off its conclusion): this is how a
        -- connective (`And ↦ And`) or a `Prop` predicate (`Pos ↦ Pos'`) — which have no type former — get a
        -- counterpart. Both directions; homogeneous heads (`List ↦ List`) coincide with the type former's entry.
        let r ← insertBidirPair types typePrefF typePrefB hA (some hB)
          (← mkConstWithFreshMVarLevels hB) (mkConstWithFreshMVarLevels hA)
        types := r.1; typePrefF := r.2.1; typePrefB := r.2.2
    | .relator .. => pure ()
  return { types, typePref := ⟨typePrefF, typePrefB⟩, terms, termPref := ⟨termPrefF, termPrefB⟩, ground }

end LeTrocq.Counterpart
