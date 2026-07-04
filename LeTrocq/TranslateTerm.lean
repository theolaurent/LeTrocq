/-
The TERM TRANSLATION `⟨·⟩` (DESIGN.md's simple term translation).

For a term/type `e` it produces ONLY the B-side counterpart `[e]` (`e` rebuilt leaf-by-leaf over `B` — NOT
`iso ∘ e ∘ iso⁻¹`). It recurses structurally (`.const`, `.fvar`, `.app`, `.lam`, `∀`, sort, `Nat` numerals)
and bottoms out at registered PRIMITIVES; an unregistered head is an ERROR — the translation never unfolds a
definition.

  ⟨c⟩        = registered counterpart (term primitive / type former / Prop predicate; else error)
  ⟨x⟩        = x'                                       (bound variable's counterpart)
  ⟨f a⟩      = ⟨f⟩ ⟨a⟩
  ⟨fun x=>b⟩ = fun x'=>⟨b⟩
  ⟨Πx:A. B⟩  = Πx':⟨A⟩. ⟨B⟩

This is HALF of the twofold translation: the RELATEDNESS `[e] : 〚T〛 e ⟨e⟩` is the graded relational
translation `[·]` in `LeTrocq.Transfer`, which is the sole consumer of `⟨·⟩` (`[t u] = [t] u ⟨u⟩ [u]`).
`translate% e` elaborates to `⟨e⟩`; the shared `Ctx`/`buildCtx`/`sym*` below serve both `⟨·⟩` and `[·]`.
-/
import LeTrocq.ParamCC
import LeTrocq.Attr
import Lean
open Lean Lean.Meta
namespace LeTrocq.Translate

/-- the `⟨·⟩` registration (COUNTERPARTS only): type formers/bases/relators ↦ B-side head; term primitives ↦
    (B-term, relatedness witness). The second component of `terms` (the relatedness) is what `[·]` reads; `⟨·⟩`
    uses only the first. A `Prop`'s counterpart comes from its RELATOR entry in `types` (`And ↦ And`,
    `Pos ↦ Pos'`); its relatedness is the graded `Param` witness `[·]` builds. -/
structure Ctx where
  types : NameMap Expr
  terms : NameMap (Expr × Expr)

/-- counterpart environment for `⟨·⟩`: `fvar ↦ x'`, the bound variable's B-side counterpart. (The graded
    translation `[·]` in `LeTrocq.Transfer` carries the relatedness separately; `⟨·⟩` needs only `x'`.) -/
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

/-- `⟨·⟩` — THE TERM TRANSLATION (DESIGN.md's `⟨·⟩`): rebuild `e`'s B-side counterpart leaf by leaf. A
    registered head maps to its counterpart (a term primitive `Nat.succ ↦ Unary.s`, a type former
    `List ↦ List`, or a `Prop` predicate `p ↦ p'`); a bound variable to its counterpart `x'`; a Π/λ/app/sort
    structurally; a `Nat` numeral through its `succ`/`zero` normal form. An unregistered head is an ERROR —
    the translation never unfolds. This produces ONLY the counterpart; the relatedness is the graded `[·]`
    in `LeTrocq.Transfer`, which calls back here for every counterpart it needs (`[t u] = [t] u ⟨u⟩ [u]`). -/
partial def term (ctx : Ctx) (env : TEnv) (e : Expr) : MetaM Expr := do
  if let some n := natNumeral? e then
    if (← whnf (← inferType e)).isConstOf ``Nat then return ← term ctx env (natExpr n)
  match e with
  | .fvar id =>
      match env.find? (·.1 == id) with
      | some (_, x') => return x'
      | none => throwError "translate: unbound variable {e}"
  | .const c _ =>
      -- one registry lookup: term primitives, then type formers/bases, then `Prop` predicates. Each stores
      -- the counterpart as its first component (the B-side term/type/predicate head).
      if let some (b, _) := ctx.terms.find? c then return b
      else if let some b := ctx.types.find? c then return b
      else throwError "translate: unregistered constant {c}"
  | .app f a => return .app (← term ctx env f) (← term ctx env a)
  | .sort _ => return e
  | .lam n A b _ => do
      let A' ← term ctx env A
      withLocalDeclD n A fun x => withLocalDeclD (n.appendAfter "'") A' fun x' =>
        return ← mkLambdaFVars #[x'] (← term ctx ((x.fvarId!, x') :: env) (b.instantiate1 x))
  | .forallE n A B _ => do
      let A' ← term ctx env A
      withLocalDeclD n A fun x => withLocalDeclD (n.appendAfter "'") A' fun x' =>
        return ← mkForallFVars #[x'] (← term ctx ((x.fvarId!, x') :: env) (B.instantiate1 x))
  | e => throwError "translate: unsupported {e}"

/-- telescope a primitive's type into abstraction-theorem triples `[a,a',aR, b,b',bR, …]`, check the binder
    count is a multiple of 3, and run `k` with the binders `xs` and their VALUE-SWAPPED reordering
    `[a',a,aR, b',b,bR, …]` (the relatedness slot stays put). The shared frame of the backward builders. -/
def withSwappedTriples (what : String) (wit : Expr) (k : Array Expr → Array Expr → MetaM Expr) :
    MetaM Expr := do
  forallTelescope (← inferType wit) fun xs _ => do
    let mut swapped : Array Expr := #[]
    for (a, a', aR) in ← chunkTriples what wit xs do
      swapped := swapped.push a' |>.push a |>.push aR     -- swap the value pair, keep the relatedness
    k xs swapped

/-- swap the (A-value, B-value) in each abstraction-theorem triple of a term primitive, giving the
    BACKWARD-direction combinator. A primitive is `cWit : ∀ a a' (aR : R a a') …, R (c …) (c' …)`
    (binders in triples); this returns `fun a' a aR … => cWit a a' aR …`. Its relatedness binder keeps the
    type `R a a'`, which is *defeq* to the symmetric relation `R.sym a' a` the backward direction supplies —
    so the same proof term serves both directions, only the value arguments swap position. -/
def symPrimitive (wit : Expr) : MetaM Expr :=
  withSwappedTriples "term primitive" wit fun xs swapped => mkLambdaFVars swapped (mkAppN wit xs)

/-- the translation context assembled from the `@[trocq]` extension, in BOTH directions: every BASE gives a
    type relation forward (`Param.R`) and backward (`Param.R ∘ Param.sym`); every TERM primitive gives its
    `c ↦ c'` map + relatedness forward, and the swapped `c' ↦ c` map + `symPrimitive` relatedness backward.
    So a term over *either* side of a registered equivalence translates by head match. -/
def buildCtx : MetaM Ctx := do
  let mut types := mkNameMap _
  let mut terms := mkNameMap _
  -- every BASE / TERM installs in both directions via `insertBidir` (the shared forward/backward +
  -- homogeneous-skip policy); the backward witness is `symPrimitive`.
  for e in trocqEntries (← getEnv) do
    match e with
    | .base hA hB tyA tyB _witName _ =>
        -- `⟨·⟩` needs only the COUNTERPART type, both directions: `⟨A⟩ = B`, `⟨B⟩ = A`.
        types ← insertBidir types hA (some hB) tyB (return tyA)
    | .term hA bTerm witName =>
        -- the backward key is the B-side head (so a homogeneous constructor like `List.cons` is skipped).
        let wit ← mkConstWithFreshMVarLevels witName
        terms ← insertBidir terms hA bTerm.constName? (bTerm, wit)
          (return (← mkConstWithFreshMVarLevels hA, ← symPrimitive wit))
    | .typeFormer hA hB _relName =>
        -- a parameterized type former `F`: `⟨·⟩` maps its head `F ↦ F'` (`⟨F a⟩ = F' ⟨a⟩`, via the `.app`
        -- rule). ONE entry, forward only.
        types := types.insert hA (← mkConstWithFreshMVarLevels hB)
    | .relator hA (some hB) _witName _cls _graded =>
        -- a RELATOR ALSO supplies `⟨·⟩` the head counterpart `P ↦ P'` (read off its conclusion): this is how a
        -- connective (`And ↦ And`) or a `Prop` predicate (`Pos ↦ Pos'`) — which have no type former — get a
        -- counterpart. Both directions; homogeneous heads (`List ↦ List`) coincide with the type former's entry.
        types ← insertBidir types hA (some hB)
          (← mkConstWithFreshMVarLevels hB) (mkConstWithFreshMVarLevels hA)
    | .relator .. => pure ()
  return { types, terms }

end LeTrocq.Translate
