# TROCQ2LEAN — Status & Next Steps

Porting [Trocq](https://arxiv.org/abs/2310.14022) (modular parametricity / proof transfer) to Lean 4
as a Lean-native reformulation. This is a **research prototype**: a Lean-native reformulation (not a
1:1 port), staged so the small `(4,4)` examples are a forward-compatible first rung of the full graded
lattice — extending additively, no rewrite.

See `lean-port-design.md` for the full design rationale. This file is the live status.

- **Toolchain:** `leanprover/lean4:v4.26.0-rc2` (elan).
- **Lake project** (`lakefile.toml`, no external deps). Layout:
  - `Trocq/` — the library (`Lattice → Hierarchy → Combinators → Solver → Tactic`; plus `Attr`+`Registry`,
    the `@[trocq]` registration, and `Translate`, the native term-level translation), via `Trocq.lean`.
    **Base-agnostic**: it registers no equivalence itself; `Trocq` builds with zero `@[trocq]` entries.
  - `Examples/` — worked examples of *using* the library: `Examples/NatUnary.lean` registers the
    `Nat ≃ Unary` base + its operations with `@[trocq]`. Not part of the library; the tests import it.
  - `Tests/` — the `lake test` suite (mirrors `Trocq/`); imports `Examples.NatUnary` for a real base.
  - `lean-port-design.md`, `STATUS.md` — docs. `arXiv-2310.14022v2/`, `trocq/` — local reference (gitignored).
- **Everything compiles** (`lake build`) **and `lake test` is green.** Axiom footprints are *pinned* by
  the test suite via `#guard_msgs in #print axioms …` (goal: nothing beyond `Quot.sound`, which
  underlies `funext` and is a kernel rule, not an added axiom).

---

## The core idea (one paragraph)

A user registers a small **base** (how `A ~ B`: a function / section / retraction / iso / equivalence /
quotient — plus primitive ops and their relatedness). Then **everything built on that base transports for
free** via a structural parametricity translation: translating a term `t_A` yields a *native* `t_B`
(rebuilt over `B` leaf-by-leaf — **not** `iso ∘ f ∘ iso⁻¹`) together with a proof `Param t_A t_B`.
Functions and lemmas are unified (both are just terms). Parametricity classes are graded pairs `(m,n)`
over the map-class lattice `{0,1,2a,2b,3,4}`; a **solver** picks the *minimal* class each occurrence
needs, and **weakening** supplies it from the registered (strong) base. The grading is what keeps proofs
cheap and what makes the univalence boundary precise.

**Lean vs Coq:** `funext` is a theorem in Lean (so `→`/`∀` at classes `≥2b` are free), but **univalence
is absent**, so the `Type` universe is hard-capped at class `2a`. (`Prop` stays richer via `propext` +
proof irrelevance, which collapses `4→3`.) This boundary is `requiresAxiom (m,n)` = "some component `≥2b`".

---

## What's done (Milestones 1–6, all compiling)

(The earlier exploratory `Examples/` prototypes — the fixed-`(4,4)` encoding probe, hand-derived
`Unary.induction`, a lambda→native-term driver, and the first hardcoded tactic — have been removed:
they're subsumed by the library + `Tests/`, except *native term translation* which is noted below as
future work. They remain in git history.)

### Milestone 6 — the full graded lattice (4 layers)

| Layer | File | What it adds | Axioms |
|---|---|---|---|
| 1 | `Trocq/Lattice.lean` | The **class algebra**: `MapClass` lattice (`le`/`join`/`meet`), `ParamClass` ops, dependency tables (`depPi`/`depArrow`/`depType`), and the **monotone least-fixpoint solver** (`Cstr` + `solve`). Validated against the paper's tables by `rfl`. | — (pure) |
| 2 | `Trocq/Hierarchy.lean` | The witness side + **weakening** (the ⇓ forget maps): six covering-edge projections composed into `MapClass.weaken : tgt ≤ src → MapHas src → MapHas tgt`, lifted to `Param.weaken` + named downgrades (`toRetraction`/`toSection`/`toFunction`/`toRel`). | none |
| 3 | `Trocq/Combinators/` | The proof-heavy **combinators** (one file per construction; `Trocq/Combinators.lean` is the umbrella): `paramArrow33` (arrow at (3,3), completeness via funext), `paramArrowLow` (same former at minimal class (0,1) — **zero proofs**), `paramType` (universe combinator at the **no-univalence ceiling** (2a,2a)). | `paramArrow33`: `[Quot.sound]` (=funext); `paramType`: **none** |
| 4 | `Trocq/Solver.lean` | **The driver, wired.** Front half: walk an `Expr`, emit `Cstr`, run the real `solve` → minimal class per occurrence (reproduces the paper's `∀A:Type,A→A` ⇒ Type→(2a,0), A→(1,1), *from the Expr*). Back half: assemble the witness via `paramArrow33` + `weaken`. | generated witness: `[Quot.sound]` |

### Graded combinator family — `Trocq/Combinators/` (one file per construction: `Arrow`/`Forall`/`Universe`)

| Combinator | Status | What it adds | Axioms |
|---|---|---|---|
| `paramArrow (m n)` | ✅ | The **arrow at EVERY output class, incl. `(4,4)`**: `arrowCov`/`arrowContra` (one arm per class) assembled with weakening; parts at the `depArrow`-**minimal** classes. The `(4,4)` coherence `R_in_mapK` is **free** — class-4 parts have subsingleton relations (`Map4Has.subsingleton`), so the arrow relation is a subsingleton and any two proofs are equal. | `[Quot.sound]` |
| `paramForall (m n)` | ✅ | The **dependent Π at EVERY output class, incl. `(4,4)`**: codomain is a *family* `pb a a' raa`. At cov `2a`+ the soundness field `map_in_R` is built by transporting the codomain fiber along the domain equivalence — `R_in_map` gives `bwd a' = a` (`subst`) and `Map4Has.subsingleton` identifies the two relatedness proofs; the `(4,4)` coherence is then free. (Caveat: a Π *over `Type`* is still capped at `(2b,2b)` by the **driver**, since there the domain witness is the universe combinator — capped at `2a` by univalence. The combinator itself is fully graded; Π over a *registered* base reaches `(4,4)`.) | `[Quot.sound]` |
| `paramTypeAtInner (m n p q)` | ✅ | universe combinator at outer class `≤ (2a,2a)` carrying **inner relation class `(p,q)`** (the `Map_Type` table — inner is free, built by weakening the reflexive identity `paramRefl`). Lets a bound type variable be supplied at *any* class, not a fixed `(1,1)`. (`paramType`/`paramTypeAt` are the `(1,1)`-inner specializations.) | none |
| `paramProp` / `paramPropAt` | ✅ | the **`Prop` universe combinator at the full `(4,4)`**: completeness is `propext`, coherence free by proof irrelevance (`PLift (P↔P')` is a subsingleton). Reaches `(4,4)` where `Type` stalls at `2a` — the precise Prop/Type asymmetry. (Handles quantifying over `Prop`; relating a *specific* prop still needs the `Sort` generalization — see below.) | `[propext]` |

**Driver fully wired** (`Trocq/Solver.lean`): the back-half `assemble req` threads the required class
top-down via `depArrow`/`depPi` and dispatches **every former to its graded combinator** at exactly that
class — `→`→`paramArrow`, `∀ A:Type,…`→`paramForall` (going under the binder), `Type`→`paramTypeAt`,
bound-var uses→the introduced relatedness witness. Parts built at the `dep*`-minimal classes, no
over-provisioning. So `transfer e root` produces the witness *directly* at `root`. Tested end-to-end:
`Nat→Nat` and nested `Nat→Nat→Nat` at `(1,0)` (computing witnesses); and the **paper flagship
`∀ A : Type, A → A` at `(0,1)`** — now *assembled* into `Param (0,1) (∀A,A→A) (∀A,A→A)`, not just inferred.

**Module dependency chain:** `Trocq.Lattice → Trocq.Hierarchy → Trocq.Combinators{.Arrow,.Forall,.Universe} → Trocq.Solver → Trocq.Tactic`
(`Trocq.Lattice` is the single source of the class algebra; `lake build` builds the chain via `Trocq.lean`).

### Boundary facts now *mechanically verified*
- Arrow/∀ at `≥2b` cost only **funext** (`[Quot.sound]`) — Lean has it → free.
- `Type` at `≥2b` costs **univalence** — Lean lacks it → universe combinator capped at `2a`,
  exactly as `requiresAxiom`/`depType` predict.
- **`Prop` universe reaches `(4,4)`** — completeness is `propext` (Lean has it), coherence is free by
  proof irrelevance. So `paramProp : Param (4,4) Prop Prop` (`[propext]`), vs `paramType` stuck at `2a`.
- **The hierarchy is over `Sort u`** (was `Type u`) — so a *specific* prop `P : Prop = Sort 0` *is* a
  valid `Param` argument, and **`Prop` goals transfer**: `∀ u : Unary, 0 ≤ toNat u` is proved from
  `∀ n, 0 ≤ n` via `paramForall` (`Tests/Combinators/Forall.lean`, `pfProp`). Proof irrelevance makes
  those `Prop` combinators reach `(4,4)` for free (`Map4Has.subsingleton`). Encoding consequence: `MapHas`
  is now bare (no `ULift` — every `MapKHas` annotated at the uniform `Sort (max u (v+1))`); the universe
  *numbering* shifted (`Type 0` is now `u=1`), so explicit `Param.{…}` annotations were dropped in favour
  of inference. `Forall` keeps its domain at `Type u` but its codomain at `Sort w` (so `Prop` bodies fit);
  `Arrow` stays over `Type u` (relating `Prop` bodies routes through `Forall`/the universe combinators).
- **Class 4 = class 3 + the relation is a subsingleton** — `Map4Has R` *implies* `Subsingleton (R a b)`
  (both related elements give equal proofs of `map a = b`, equal by Lean's proof irrelevance). So the
  `(4,4)` coherence `R_in_mapK` is free wherever the relation comes from class-4 data. This is the precise
  Lean form of "no univalence ⇒ 4 collapses to 3 (on h-props)".

---

## What's next (toward a real tool)

Ordered roughly by leverage. The prototype is forward-compatible: each item extends, none rewrites.

1. **Full graded combinator family** — ✅ **COMPLETE.** Arrow, dependent Π, and the universe are all
   built at *every* class up to their true Lean boundary: arrow `(4,4)`, Π `(4,4)` (combinator;
   `(2b,2b)` when over `Type` via the driver, by univalence), universe `(2a,2a)` with `Map_Type` inner up
   to `(4,4)`. The driver assembles every former at its minimal per-node class, under binders, with
   bound variables at their solved class, and propagates full `(4,4)` equivalences end-to-end. The `(4,4)`
   coherence and the dependent-Π soundness transport are both done (free via subsingleton + `subst`).
   *Open extension (not a combinator limit):* the driver's `gen` doesn't yet handle `∀ (n : Base), …`
   (dependent Π over a registered base), so Π's `(4,4)` reach is only exercised via direct combinator use.

2. **User surface** — ✅ **done** (`Trocq/Tactic.lean`): `transfer% T` elaborates to the witness
   `Param (4,4) T T'` (so `(transfer% (Nat→Nat)).cov.map` *is* the transported function, and it
   computes); `trocq` transfers the current goal to its counterpart and refines by the backward map.
   The driver's `gen`/`assemble` now handle **dependent Π over a registered base** (`∀ (x : Base), …`)
   and a **generic `app` node** (the abstraction-theorem rule `⟦head x⟧ = ⟦head⟧ x x' xR` for a
   registered constant `head`) — so `trocq` transfers real **`Prop` goals** end-to-end:
   `example : ∀ u : Unary, Pos u := by trocq; exact fun n => Nat.zero_le n` (reduces to `∀ n, Pos' n`).
   *Open:* still hard-wired to `Nat ≃ Unary` + the demo constant `Pos` (needs item 3, `@[trocq]`);
   `app`'s argument is currently a bound base variable (nested apps / `app`-of-`app` not yet).

3. **Registration** — ✅ **done** (`Trocq/Registry.lean` + `Trocq/Attr.lean`): `@[trocq]` attribute +
   env extension. Tagging a witness classifies it **eagerly** (`parseEntry`, run in the attribute's `add`)
   from its type into **base** (`Param m n A B`, both directions auto via `Param.sym`), **relator**
   (`∀…, Param … (P …)(P' …)`, keyed by head `P`), or **term primitive** (`∀…, R … (c …)(c' …)`, `c ↦ c'`),
   and stores the parsed `RegKind`. So a malformed witness is rejected right at the tag site
   (`@[trocq] def bogus : Nat := 5` ⤳ error there). Per-surface builders (`Solver.buildAtoms`/`buildConsts`,
   `Translate.buildCtx`) just read the stored entries; `transfer%`/`trocq`/`translate%` use them — nothing
   hardcoded. A predicate `@[trocq]`-registered in a *user* file is picked up by `trocq` with no library
   change (`Tests/Tactic.lean`). *Open:* universe-polymorphic witnesses (parser uses `mkConst`, no levels);
   registering from a Mathlib `Equiv` (item 4).

4. **Mathlib reuse** — wire `Equiv` (registration menu), `Relator.LiftFun` (= `RArrow`), `Quot`
   (funext path) instead of bespoke definitions.

5. **Native term/program transport** — ✅ **done** (`Trocq/Translate.lean`): the full term-level
   parametricity translation `⟦·⟧`. For any term `t : T` the mutual `param`/`paramType` produce both the
   native counterpart `t'` (rebuilt over `B` leaf-by-leaf, *not* iso-conjugation) and the relatedness
   `tR : ⟦T⟧ t t'`. Structural over `.lam`/`.app`/`∀`(arrow+dependent Π)/`.sort`/`.fvar`; bottoms out at
   registered **primitives** and **unfolds** any other constant's definition (so `double` transports via
   `Nat.succ`/`Nat.zero` alone — item 1). `translate% t` ⤳ `t'`, `relate% t` ⤳ `tR`. Handles
   polymorphism (`fun (A:Type)(a:A) => a`). *Open frontier:* **recursors / `match`** (→ generate the
   `Unary` induction principle from `Nat.rec`), `match`-compiled defs, and `Nat`-literal/instance leaves.

See `lean-port-design.md` §10 for the original phased plan.

---

## Quick build reference

```sh
lake build    # build the whole Trocq library
lake test     # run the test suite (fails on any regression)
```
