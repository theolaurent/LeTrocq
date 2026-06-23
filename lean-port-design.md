# Trocq → Lean 4: a Lean-native reformulation (design exploration)

> **HISTORICAL — this is the original pre-implementation design exploration (kept for the *rationale*).**
> For the live state of the actual implementation see **`STATUS.md`**. The high-level analysis here held
> up well (§2 on proof-irrelevance `4≃3`, funext-free / univalence-absent; §◆ "register a base, transport
> everything"). The concrete proposals were superseded as the code was built:
> - **Encoding (§4):** the indexed `MapHas` is real, but over **`Sort u`** (not `Type u`) with all six
>   `MapKHas` annotated at a uniform universe (no `ULift`) — so `Prop` is a first-class argument.
> - **Assembly (§5):** done by a **metaprogram driver** (`Trocq/Solver.lean`), not typeclass resolution.
> - **Universe (§2b):** the `Type` universe is capped at `2a` as predicted, but the **`Prop` universe
>   reaches `(4,4)`** via `propext` (`paramProp`) — a refinement of "≥2b is impossible, full stop".
> - **§10 plan / §11 open questions** are largely done (see `STATUS.md`).

Status: design / research note. Goal is to explore what Trocq *should* look like reborn in
Lean 4 — leaning on Lean idioms (typeclasses, `Quot`, proof irrelevance, `MetaM`) rather than
transliterating the Coq + coq-elpi implementation. Code blocks are **sketches** meant to pin
down the architecture, not compile-ready Lean.

References: paper `arXiv-2310.14022v2/main.tex`; upstream `trocq/` (Coq theory + Elpi plugin).

---

## 0. TL;DR of the recommended architecture

1. **Lattice** (`MapClass`, `ParamClass = MapClass × MapClass`, order/meet/join, `depPi`/`depArrow`
   tables): ported verbatim as a tiny pure module. Unchanged from Trocq — it's already minimal.
2. **Hierarchy**: replace Trocq's 36 Elpi-*generated* `Paramₘₙ.Rel` records with **one indexed
   structure** `Param (m n : MapClass) (A B)` whose field *types* are computed by recursion on the
   class (dependent types do the codegen's job).
3. **Combinators** (`Param_arrow`, `Param_forall`, `Param_Type`, weakenings, sym, id): a small
   fixed library of lemmas, parameterised by class.
4. **Witness supply for leaves** (constants / registered relations): **typeclass resolution** + an
   `@[trocq]` attribute, replacing Trocq's bespoke Elpi DB lookup.
5. **Class inference**: keep an explicit **monotone fixpoint solver over the finite lattice**
   (Trocq's constraint graph, re-expressed as a worklist in a state monad). *Not* typeclass search.
6. **Driver**: a `MetaM`/`TacticM` traversal over `Expr` that emits constraints, solves them, then
   builds the related goal `G'` and the `comap`-wrapped proof. Surfaced as a **tactic** `trocq`
   (plus a term elaborator `transfer%`), **not** a pure `macro` — it is type-directed.

The two genuinely Lean-native wins: (3)+(4) let **typeclass resolution assemble most of the
witness automatically**, and Lean's foundations turn Trocq's "minimise univalence" optimisation
into a simpler "stay inside a hard boundary" constraint (§2).

---

## 1. What carries over unchanged, what gets rethought

| Trocq component | Lean-native disposition |
|---|---|
| Map-class lattice + `depPi`/`depArrow` tables (`elpi/class.elpi`) | **Port verbatim.** Pure, finite, already minimal. |
| 36 generated `Paramₘₙ.Rel` records (`elpi/generation/*`) | **Replace** with six named `MapKHas` structures + an indexed `MapHas`/`Param m n A B` (§4, validated). No codegen. |
| `Param_arrow` / `Param_forall` / `Param_Type` combinators | **Port** as ~12 lemmas; expose as instances where possible. |
| Forgetful weakenings `⇓` | **Port**; derive by recursion on the class order. |
| Elpi `trocq.db` + `Trocq Use` | **Replace** with `@[trocq]` attribute → env extension + typeclass instances. |
| CHR constraint graph (`elpi/constraints/*`) | **Re-express** as explicit worklist/fixpoint in `StateRefT`. |
| `param.elpi` translation (HOAS) | **Rewrite** over `Expr` with `withLocalDecl`/telescopes. |
| `tactic.elpi` driver (`comap` term, refine) | **Rewrite** as `TacticM`. |
| HoTT base (`hott/`) vs axiomatised (`std/`) split | **Collapse to one build** ≈ `std`: Lean *is* proof-irrelevant `Eq`. |
| match/fix translation | **Out of scope** (as upstream): recursors are registered constants. |

---

## ◆ User-facing model: register a base, transport everything (settled in design discussion)

The intended workflow, and the principle that should drive the surface API:

- The user **registers a small base**: *how A relates to B* — chosen from a menu (`function` / `section` /
  `retraction` / `iso` / `equivalence` / `quotient`), **not** raw `(m,n)` classes — plus the genuinely
  *primitive* operations on A with their B-counterparts and relatedness proofs. This is the only hand
  work; it is one-time and small (≈ Trocq's `Trocq Use`).
- **Everything built on that base transports for free**, via the *structural parametricity
  translation* — *functions and lemmas alike, by one and the same recursion*. In a dependently typed
  setting both are just terms: translating a term `t_A` yields a term `t_B` **and** a proof
  `Param t_A t_B`. There is no separate "function transport" vs "lemma transport".
- The synthesized `t_B` is **native**: the translation rebuilds the body over B *leaf-by-leaf*,
  substituting registered counterparts. It is emphatically **not** iso-conjugation
  (`iso ∘ f ∘ iso⁻¹`); the output uses B's own operations and computes natively. (Conjugation is the
  thing to avoid; this was an explicit design correction.)
- **Boundary:** the recursion bottoms out at *registered leaves*. Derived terms = free; primitive
  leaves (recursors, axioms, opaque monomorphic constants) = register once. Polymorphic leaves are
  free *in principle* (the free theorem) though still registered for the concrete witness term.

**Architectural consequence.** The `param` driver (§8) must **return the translated term**, not merely
discharge a goal — Trocq's predicate already does (`param … X' XR`). Build the driver *term-first*;
the tactic is just one consumer (points it at the goal *type*, discharges via `comap`), and a
`transfer%` term-elaborator / `#transfer` command is another consumer (keeps `t_B` as a definition).

**Scope (DECIDED): the full graded lattice is the destination. The `(4,4)` prototype is a
forward-compatible first rung, not an iso-only tool.** Staging, not a fork. Hard constraints on the
prototype so the lattice slots in *additively* (no rewrite):
- Use the real `MapClass`/`ParamClass` + the six-structure `MapHas` **everywhere**; never special-case
  "iso" as a bespoke path.
- The `param` driver takes a **target class as a parameter** even while we only ever pass `(4,4)`; the
  solver (§6) later just changes *who supplies the class*, not the traversal.
- Registration **stores classes** from day one (all `(4,4)` now, arbitrary later).
- **No `(4,4)`-only shortcuts** that assume both directions exist / totality / symmetry — those break
  at sections/retractions.
- "functions vs lemmas" is **not** a fork — unified by the bullet above.

---

## 2. Foundational decisions (where Lean ≠ Coq/HoTT matters)

**(a) `Eq` is proof-irrelevant and lives in `Prop`.** Trocq's `std` build already commits to this.
Consequence worth exploiting: when a relation `R` is **`Prop`-valued**, the coherence field
`R_in_mapK : map_in_R (R_in_map r) = r` is *free* (proof irrelevance), so `Map4 ≃ Map3` and the top
of the tower partly collapses. For the very common case of transferring `Prop` goals over `Prop`
relations, the engine can shortcut `four → three`. Keep the full lattice (data-valued relations on
`Type` still need the distinction), but special-case `Prop` for speed and to avoid spurious
obligations.

**(b) Funext is a theorem, univalence does not exist.** In Trocq, classes with a component `≥ 2b`
require an axiom; the inference *minimises* axiom usage. In Lean:
  - `funext` is provable (from `Quot`). So the `Param_arrow`/`Param_forall` combinators at
    `2b/3/4` — which need funext in Coq — are **unconditionally available**. The `` `{Funext} ``
    hypotheses simply vanish.
  - Univalence is **absent**. So relating the **universe to itself** (`Param_Type`) at any class
    with a component `≥ 2b` is **impossible, full stop** — not merely expensive.

  Net effect: the `requires-axiom` boundary becomes a **hard constraint on `Sort` occurrences
  only**: every transferred `Type`/`Sort` must land in `{0,1,2a}²`. Inference's job shifts from
  "minimise univalence" to "find a least solution that keeps every sort-class in the axiom-free
  region." Same solver, different (simpler, total) acceptance test. Everything that is *not* a bare
  universe occurrence — functions, `∀`, registered inductives — can still reach `(4,4)`.

**(c) `Quot` as the source of the few axioms we do want.** funext, and propext if needed, come from
`Quot`/Lean core. No new axioms introduced by the framework itself. A `trocq`-produced proof should
ideally cite only `funext`/`propext` (checkable via `#print axioms`), mirroring Trocq's
"`Print Assumptions` shows no univalence" demos.

**(d) Universe handling.** Lean universe polymorphism is cleaner than Coq's annotated cumulativity.
Keep source universes on target sorts (Trocq does the same). The `Param` structure is universe-
polymorphic; relation values can be placed in `Type v` independent of `A B : Type u`.

---

## 3. The class lattice (port verbatim)

```lean
inductive MapClass | zero | one | twoA | twoB | three | four
deriving DecidableEq, Repr

abbrev ParamClass := MapClass × MapClass

namespace MapClass
-- the diamond:  zero < one < {twoA, twoB} < three < four   (twoA ⊥ twoB)
def le : MapClass → MapClass → Bool         -- hand table
def join : MapClass → MapClass → MapClass    -- lub
def meet : MapClass → MapClass → MapClass    -- glb
-- minimal dependency tables, transcribed from elpi/class.elpi:
def depPi    : MapClass → ParamClass × ParamClass   -- (domain class, codomain class)
def depArrow : MapClass → ParamClass × ParamClass
end MapClass

namespace ParamClass
def le (a b : ParamClass) : Bool := a.1.le b.1 && a.2.le b.2
def join / meet : componentwise
def negate (c : ParamClass) : ParamClass := (c.2, c.1)
def requiresAxiom (c : ParamClass) : Bool := !c.1.le .twoA || !c.2.le .twoA  -- (component ≥ 2b)
def depPi    (c : ParamClass) : ParamClass × ParamClass := ...  -- combine via join/negate
def depArrow (c : ParamClass) : ParamClass × ParamClass := ...
def bottom := (.zero, .zero)   def top := (.four, .four)
end ParamClass
```

This module is ~150 lines, pure, and unit-testable against the paper's tables. It is the spine of
the whole system; get it byte-identical to `elpi/class.elpi` first.

---

## 4. The hierarchy: six named map-levels, indexed (vs Trocq's 36 generated records)

> **VALIDATED in Lean 4 (v4.26.0-rc2)** — see `lean-proto/Defeq.lean`. The first-cut "Σ-tower"
> idea did *not* survive contact with Lean's universe rules; the working encoding below does, and
> answers open question #4 affirmatively (definitional reductions hold by `rfl`).

Trocq generates `Param00 … Param44` with Elpi because Coq can't compute a record's field set from a
value. In Lean we don't need 36 records, but **two facts forced a redesign** of the naïve approach:

- **(F1) No universe cumulativity.** Lean 4 (unlike Coq) does *not* have `Type u ≤ Type (max u v)`.
  The six levels genuinely inhabit different universes: levels `{0,1,2b}` carry only `map : A→B`
  (data) plus `Prop` fields → `Type u`; levels `{2a,3,4}` carry `map_in_R : ∀ a b, map a = b → R a b`
  whose codomain `R a b : Type v` → `Type (max u v)`. A single `MapHas : MapClass → … → Type ?`
  must land in the join `Type (max u v)` and **`ULift` the three small levels**.
- **(F2) `Σ`/`×` are Type-only.** `R_in_map`'s body is an `Eq` (a `Prop`), and `Sigma`/`Prod` reject
  `Prop` components. So the per-level bundle must be a `structure` (Lean structures mix Type/Prop
  fields freely), not a Σ-tower.

The resolution kills two birds: index over **six named structures** (not 36, not Σ-towers). We still
avoid Trocq's codegen *and* we keep **named projections** (better errors — this also resolves the
ergonomics half of open question #1 in favour of "no codegen needed").

```lean
universe u v
structure Map0Has {A B : Type u} (_R : A → B → Type v) : Type u where
structure Map1Has {A B : Type u} (_R : A → B → Type v) : Type u where
  map : A → B
structure Map2aHas {A B : Type u} (R : A → B → Type v) where      -- : Type (max u v)
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
structure Map2bHas {A B : Type u} (R : A → B → Type v) : Type u where
  map : A → B
  R_in_map : ∀ a b, R a b → map a = b
structure Map3Has {A B : Type u} (R : A → B → Type v) where       -- : Type (max u v)
  map : A → B ;  map_in_R : ∀ a b, map a = b → R a b ;  R_in_map : ∀ a b, R a b → map a = b
structure Map4Has {A B : Type u} (R : A → B → Type v) where       -- : Type (max u v)
  map : A → B ;  map_in_R : ∀ a b, map a = b → R a b ;  R_in_map : ∀ a b, R a b → map a = b
  R_in_mapK : ∀ a b r, map_in_R a b (R_in_map a b r) = r

/-- Class-indexed bundle; `ULift` pads the three "small" levels up to `Type (max u v)`. -/
def MapHas : MapClass → {A B : Type u} → (A → B → Type v) → Type (max u v)
  | .mZero,  _, _, R => ULift.{v} (Map0Has R)
  | .mOne,   _, _, R => ULift.{v} (Map1Has R)
  | .mTwoA,  _, _, R => Map2aHas R
  | .mTwoB,  _, _, R => ULift.{v} (Map2bHas R)
  | .mThree, _, _, R => Map3Has R
  | .mFour,  _, _, R => Map4Has R

structure Param (m n : MapClass) (A B : Type u) where
  R      : A → B → Type v
  cov    : MapHas m R
  contra : MapHas n (fun b a => R a b)
```

Projections read the named field through the `ULift` where present (`P.cov.down.map` at level 1,
`P.cov.map` at level 2a), guarded by a class inequality. **Tested:** `(funParam f).map = f := rfl`
and `(funParam (·+1)).map 3 = 4 := rfl` — i.e. projections reduce *and compute*.

Cost of the encoding: one `.down` on the three ULifted levels (cheap, reduces by `rfl`), and a hard
requirement that the engine carry universe levels carefully (the `Param_Type` combinator's relation
universe is `max u (v+1)`, one above the type universe — Lean needs these spelled out, see proto).

---

## 5. Combinators, and the Lean-native win: assembly by typeclass resolution

The arrow/forall/sort combinators are a fixed, small library:

```lean
def R_arrow (PA : Param 0 0 A A') (PB : Param 0 0 B B') : (A → B) → (A' → B') → Type _ :=
  fun f f' => ∀ a a', PA.R a a' → PB.R (f a) (f' a')

-- one per output map-class, input classes dictated by depArrow:
def Param_arrow (c : ParamClass)
    (PA : Param (depArrow c).1.1 (depArrow c).1.2 A A')
    (PB : Param (depArrow c).2.1 (depArrow c).2.2 B B') :
    Param c.1 c.2 (A → B) (A' → B') := ...     -- funext used internally at 2b/3/4

def Param_forall (c) (PA …) (PB : ∀ a a', PA.R a a' → Param … (B a) (B' a')) :
    Param c.1 c.2 (∀ a, B a) (∀ a', B' a') := ...

def Param_Type (c) (h : ¬ c.requiresAxiom) :        -- ONLY axiom-free classes exist in Lean
    Param c.1 c.2 (Type u) (Type u) := ...           -- R := Param (4,4) … ; cov from id/transport
```

**The win.** In Trocq, `param.elpi` *explicitly* picks and applies these combinators and chases the
DB for leaves. In Lean we can make leaf resolution and even structural assembly **driven by
instance search**, once the classes are fixed:

```lean
class HasParam (c : ParamClass) (A B : outParam Type) where
  witness : Param c.1 c.2 A B

@[trocq] instance : HasParam (4,4) Nat BinNat := ⟨RN⟩      -- user registration (see §7)
instance [HasParam (depArrow c).1 A A'] [HasParam (depArrow c).2 B B'] :
    HasParam c (A → B) (A' → B') := ⟨Param_arrow c ‹_› ‹_›⟩
```

So *if the class on every node is already decided*, the entire witness can be synthesised by one
`synthInstance (HasParam c G G')` call — Lean's resolution does the structural recursion that
`param.elpi` does by hand. This is strictly more idiomatic and removes a large chunk of the driver.

**Why we still can't let typeclasses pick the classes.** TC resolution finds *some* instance via
backtracking; we need the *least* class assignment, and an unconstrained search over `(m,n)` is
exactly the exponential blow-up the Trocq authors avoided. So the classes stay outputs of the
dedicated solver (§6); TC only supplies witnesses *after* classes are ground. Division of labour:

> **solver → classes (minimal, total over the lattice); typeclass search → witnesses (given classes).**

---

## 6. Class inference: the lattice solver

The hard, irreducible piece. Trocq seeds the goal with a target class, attaches a *class variable*
to every `Sort` occurrence, traverses once emitting constraints, and computes the least solution.

Re-expressed for Lean:

```lean
structure CVar where id : Nat          -- one per Sort occurrence
inductive Constraint
  | geq      (x : CVar) (y : Bound)               -- x ≥ lower bound (var or const)
  | depPi    (out : CVar) (dom cod : CVar)        -- out drives dom,cod via depPi table
  | depArrow (out : CVar) (dom cod : CVar)
  | depType  (out : CVar) (rel : CVar)            -- sort: rel-class driven by out, + axiom guard
  | depConst (gref : Name) (cls : List CVar) (out : CVar)  -- registered constant's classes

abbrev Solve := StateRefT SolverState MetaM
```

The solver is a **monotone fixpoint over a finite lattice**, so it terminates and is cheap:
1. topologically order nodes (dependency precedence; cycles handled as in Trocq's
   `constraint-graph.elpi`);
2. for each node, `minClass = join` of all lower bounds; check `minClass ≤ maxClass` (`meet` of
   upper bounds); for **sort** nodes additionally enforce `¬ requiresAxiom minClass` (the Lean hard
   boundary, §2b) — failure here is the honest "this transfer needs univalence, unavailable" error;
3. instantiate, rewriting each `depPi/depArrow/depType/depConst` edge into plain `geq` bounds once
   its driving class is known (exactly Trocq's `instantiate.aux`).

This is ~300–400 lines but entirely pure and directly mirrors `constraint-graph.elpi` +
`constraints-impl.elpi` (minus the CHR plumbing, which Lean doesn't need). It is the part to port
most faithfully — the algorithm is subtle and already proven out upstream.

Seeds: the tactic seeds the goal at `(0,1)` (gives `comap : G' → G`); the coercion/term use seeds
`(1,0)` (gives `map : G → G'`).

---

## 7. Registration: `@[trocq]` attribute, env extension, instances

Replace the Elpi DB with Lean-native registration. A user proves a relatedness lemma at whatever
class they can, and tags it:

```lean
@[trocq] def RN : Param .four .four BinNat Nat := Iso.toParam BinNat.natIso
@[trocq] def RN0 : RN.R 0 0 := ...
@[trocq] def RNS : ∀ m n, RN.R m n → RN.R (m+1) (n+1) := ...
```

The attribute handler (a `command_elab`/attribute):
1. reads the lemma's type, extracts `(gref_src, gref_tgt, output-class, arg-classes)` exactly as
   `param-class-util.elpi : type->classes` does (every `Param i j _ _` argument contributes class
   `(i,j)`);
2. stores an entry in a `SimplePersistentEnvExtension` keyed `(Name, ParamClass, List ParamClass)`;
3. **auto-generates the weakenings**: for every lower output class, emit a `HasParam` instance that
   forgets fields (Trocq pre-generates weakened constants; in Lean these can be lazy instances
   `HasParam c' … ← HasParam c …` with `c' ≤ c`).

`trocq using RN RN0 RNS` / `trocq with <relationName>` scopes which entries are live, matching
Trocq's `RelatedWith`.

Multiple manual versions at incomparable classes (the upstream "`listR` stuck at (4,4)" fix) are
just multiple tagged lemmas — instance resolution picks the applicable one.

---

## 8. Driver and user surface

The translation itself (`param.elpi` analogue) over `Expr` in `MetaM`:

```lean
partial def param (cl : CVar) (e : Expr) : Solve (Expr × Expr) := do
  -- returns (e', proof : Param cl.. e e')   [classes still symbolic until solve]
  match e with
  | .sort .. => emit (.depType cl ?rel); pure (e, mkParamType …)
  | .forallE .. =>   -- distinguish arrow vs dependent Π
      if dependent then emit (.depPi cl ?a ?b); ... mkParamForall
      else            emit (.depArrow cl ?a ?b); ... mkParamArrow
  | .lam .. => withLocalDecl … (store fvar ↦ (x', xR, classOfDom)); recurse body
  | .app .. => param head; for each arg expand to triple (x, x', xR); weaken result
  | .const n .. => emit (.depConst n ?cls cl); lookup via HasParam after solve
  | .fvar f => read the stored (x', xR) from the binder context
```

Binders: Trocq's `@param-pi-decl` (introduce `x, x', xR` and remember `param.store x ↦ …`) becomes
`Meta.withLocalDecl` introducing the three fvars and a `HashMap FVarId (Expr × Expr × ParamClass)`
in `SolverState`. Argument tripling (`x ↦ x, x', xR`) is identical.

Two-pass shape: **pass 1** traverse emitting constraints + a *deferred* witness skeleton (with class
metavariables); **solve**; **pass 2** instantiate classes, then `synthInstance`/named-combinator
calls fill the now-ground witness. (Or single pass with postponed instance problems.)

Final assembly (tactic): `⟨G', proof⟩ ← param (0,1) G`; build `(P.comap _ : G' → G) (?new : G')`;
`refine` leaving `?new : G'` as the goal. Term elaborator `transfer% e to T` does the `map`
direction. A Lean **coercion** hook (analogous to `CoercionFallbackTactic`) is optional/phase-2.

Surface syntax:
```lean
syntax (name := trocqTac) "trocq" (" to " term)? (" using " ident+)? : tactic
elab_rules : tactic | `(tactic| trocq $[to $g]? $[using $rs*]?) => ...
```

> **"Macro" caveat.** The request was "as a macro," but Trocq is *type-directed* (it inspects the
> goal's type and infers classes), so it must be an `elab`/`TacticM` metaprogram, not a syntactic
> `macro`. The user-facing trigger is still a single `trocq` token, so it *feels* like a macro.

---

## 9. Reuse of existing Lean / Mathlib infrastructure

- **`Relator.LiftFun` (`R ⇒ S`)** in Mathlib *is* `R_arrow` for `Prop`-relations — the same
  parametricity arrow already used by `to_additive`'s relator machinery. Worth aligning with so
  Trocq-Lean interoperates with existing transfer lemmas.
- **`Equiv` / `Equiv.arrowCongr` / `Equiv.piCongr`** correspond to the `(4,4)` combinators; can seed
  the equivalence-strength instances. `Iso.toParam` ≈ build `Param (4,4)` from an `Equiv`.
- **`Function.Injective`/`Surjective` + a chosen inverse** give `(4,2b)` sections / `(4,2a)`
  retractions — the non-equivalence transfers that are Trocq's headline capability.
- **`Quot`** supplies `funext` (and `propext`), the only axioms a Lean Trocq should rely on.
- Mathlib already has `Mathlib.Logic.Equiv.TransferInstance` and assorted ad-hoc transfer; positioning
  Trocq-Lean as the *general* engine these special cases factor through is a compelling pitch.

---

## 10. Phased plan

0. **[DONE]** Encoding validated (`lean-proto/Defeq.lean`) and a hand-assembled end-to-end transfer
   (`lean-proto/Minimal.lean`): `Nat≃Unary` registered as `Param (4,4)`, `Unary` induction derived
   from `Nat.rec`, `#print axioms` ⇒ none. Confirms the hierarchy + the "register a base" model concretely.
1. **Lattice module** (§3) + property tests vs paper tables. (small, self-contained)
2. **Hierarchy** `MapHas` + `Param` + projections + a hand-built `(4,4)` from `Equiv`, `(4,2a)` from
   split surjection (§4). Prove `Param` for `Bool`, `Nat`/`BinNat` by hand (the `Param_bool.v`
   template). (no metaprogramming yet)
3. **Combinators** `Param_arrow`, `Param_forall`, `Param_Type` (axiom-free classes), weakenings,
   `sym`, `id` (§5). Expose as `HasParam` instances; confirm `synthInstance` assembles a witness for
   a *fixed* class on a small closed goal.
4. **Term-first driver** (§8, the ◆ model) on the λ/app/const fragment, **fixed class `(4,4)`, no
   solver**: traverse a *term* `t_A`, emit native `t_B` + `Param t_A t_B` by structural translation
   over registered leaves. First demo: rebuild a `Nat→Nat` function as a native `Unary→Unary` one with
   relatedness, axiom-free — *generated*, replacing the hand-written `transfer_induction`. (Turns
   proto Minimal.lean's manual term into an automated one.)
5. **Tactic on top** — point the driver at a goal *type*, discharge via `comap`; `transfer%` term
   elaborator keeps `t_B` as a def. Reproduce the `Nat`-induction transfer with the tactic.
6. **Solver** (§6) + Π/→/universe at general classes — the full graded lattice (the destination, §◆).
   Then **registration** `@[trocq]` + `using`/`with` (§7) and the retraction `(4,2a)` / section
   `(4,2b)` examples (modular arithmetic, summable sequences) — the novel cases.
7. Ergonomics: coercion hook, error messages, `Prop` fast-path (§2a).

Milestone 4 is the first *generated* artefact (function transport, fixed-(4,4), no solver); the solver
(6) is deferred until the relation-strength scope is decided.

---

## 11. Open research questions / risks

- **[ANSWERED ✓] Definitional-equality demands.** *Verified in `lean-proto/Defeq.lean`
  (Lean v4.26.0-rc2).* `(Param_Type ..).R ≡ Param α` holds by `rfl`; a bound `A_R : (Param_Type..).R A B`
  typechecks at `Param α A B` with **no cast**; projections through the ULifted `MapHas` reduce *and
  compute* (`(funParam (·+1)).map 3 = 4 := rfl`). A negative control (`(3:Nat)=4 := rfl` is rejected)
  confirms the checks are non-vacuous. The indexed encoding does **not** bite here. The abstraction-
  theorem's key defeq is therefore safe under this encoding.
- **[ANSWERED ✓] Indexed vs generated records.** Resolved in favour of **no codegen**: index a
  6-way `MapHas` over six *named* `MapKHas` structures (§4). Keeps named projections (good errors),
  needs no metaprogram. The 36-record Σ-tower variant is abandoned (broke on F1/F2 below).
- **[NEW, surfaced by the experiment] No universe cumulativity (F1) + `Σ` is Type-only (F2).**
  Lean lacks `Type u ≤ Type (max u v)`, and `Sigma`/`Prod` reject the `Prop` (`Eq`) components. Both
  are now handled (named structures + `ULift` on levels {0,1,2b}, §4). *Residual risk:* the engine
  must thread universe levels explicitly (the `Param_Type` relation lives at `max u (v+1)`); sloppy
  universe handling will produce "stuck universe constraint" errors. Budget real effort for universe
  bookkeeping in the driver — more than a naïve port would assume.
- **Solver/TC interleaving** — can we run class-solving and instance synthesis in one fixpoint via
  *postponed* TC problems, or must it be strict two-phase? Two-phase is safe; one-phase is nicer.
- **`Prop` vs `Type` relations** — formalise the `four→three` collapse (§2a) and decide whether the
  engine should *prefer* `Prop`-valued relations for `Prop` goals (likely yes; big ergonomics win in
  Mathlib-style developments).
- **Universe-polymorphic registration** — making `@[trocq]` entries universe-polymorphic cleanly
  (the proto already shows the levels involved: `Param.{u, v}` for values, `Param.{u+1, max u (v+1)}`
  for the universe combinator).
- **No-match/fix scope** — confirm the registered-recursor approach covers the intended Mathlib
  targets, or scope a later `match`/`fix` extension (a real research increment beyond upstream).
- **Soundness story** — Trocq's guarantee is *the produced term typechecks* (no separate trusted
  kernel claim needed); Lean inherits this for free since the kernel rechecks `refine`d terms. Good:
  the engine can be buggy without producing unsound proofs.
```
