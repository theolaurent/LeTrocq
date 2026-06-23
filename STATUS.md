# TROCQ2LEAN — Status & Next Steps

Porting [Trocq](https://arxiv.org/abs/2310.14022) (modular parametricity / proof transfer) to Lean 4
as a Lean-native reformulation. This is a **research prototype**: a Lean-native reformulation (not a
1:1 port), staged so the small `(4,4)` examples are a forward-compatible first rung of the full graded
lattice — extending additively, no rewrite.

See `lean-port-design.md` for the full design rationale. This file is the live status.

- **Toolchain:** `leanprover/lean4:v4.26.0-rc2` (elan).
- **Lake project** (`lakefile.toml`, no external deps). Layout:
  - `Trocq/` — the library (`Lattice → Hierarchy → Combinators → Solver`), exposed via `Trocq.lean`.
  - `Tests/` — the `lake test` suite (one module per layer); hard assertions, fails on regression.
  - `Examples/` — standalone fixed-`(4,4)` demos (not part of any target; run individually).
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

### Foundations — `Examples/` (standalone fixed-class `(4,4)` artifacts)

These predate the layered library and each carry their own copy of the encoding (old `mZero…` naming).
They are kept as demos because several show capabilities the library doesn't expose yet (lambda→native-term
translation, the tactic). Run with `lake env lean Examples/<File>.lean`.

| File | What it establishes | Axioms |
|---|---|---|
| `Examples/Defeq.lean` | The **encoding**: 6 graded `MapKHas` structs + indexed `MapHas` (ULift on small levels) + `Param m n A B`. Answers open-q #4: abstraction-theorem defeq holds by `rfl`; projections compute. | — |
| `Examples/Minimal.lean` | Hand-written transfer: registers `Nat ≃ Unary` as a `(4,4)` witness `RN`; a generic `transfer_induction` derives `Unary.induction` **for free** from `Nat.rec`. | none |
| `Examples/Driver.lean` | Term-first **parametricity-translation driver** (metaprogram over `Expr`). Generates native `f.B := fun u => u.s.s` + `Param` proof from `f := fun n => n.succ.succ`. | none |
| `Examples/Induction.lean` | Driver extended to **higher-order / dependent** terms (sorts, dependent `Π`, applied predicates). Generates the `Unary` induction principle. | none |
| `Examples/Tactic.lean` | The first **`trocq` tactic**: `by trocq` transfers a `Unary` goal to the (easier) `Nat` goal via the comap direction. | none |

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
| `paramArrow (m n)` | ✅ | The **arrow at every output class** `≤ (3,3)`: `arrowCov`/`arrowContra` (one arm per class) assembled with weakening; parts required only at the `depArrow`-**minimal** classes (a bound var at `(1,1)` is enough — no over-provisioning). `map4` deferred (the (3→4) adjoint coherence). | `[Quot.sound]` |
| `paramForall (m n)` | ✅ | The **dependent Π at output `≤ (2b,2b)`**: codomain is a *family* `pb a a' raa` (the relatedness indexes the codomain relation). Capped at `2b` because output cov `2a`/`3` need the domain at `map4` *with* `R_in_mapK` — Π hits the adjoint-coherence wall earlier than arrow. | `[Quot.sound]` |
| `paramType` / `paramTypeAt (m n)` | ✅ | universe combinator at every class `≤ (2a,2a)` (`paramTypeAt` weakens the `(2a,2a)` ceiling). | none |

**Driver fully wired** (`Trocq/Solver.lean`): the back-half `assemble req` threads the required class
top-down via `depArrow`/`depPi` and dispatches **every former to its graded combinator** at exactly that
class — `→`→`paramArrow`, `∀ A:Type,…`→`paramForall` (going under the binder), `Type`→`paramTypeAt`,
bound-var uses→the introduced relatedness witness. Parts built at the `dep*`-minimal classes, no
over-provisioning. So `transfer e root` produces the witness *directly* at `root`. Tested end-to-end:
`Nat→Nat` and nested `Nat→Nat→Nat` at `(1,0)` (computing witnesses); and the **paper flagship
`∀ A : Type, A → A` at `(0,1)`** — now *assembled* into `Param (0,1) (∀A,A→A) (∀A,A→A)`, not just inferred.

**Module dependency chain:** `Trocq.Lattice → Trocq.Hierarchy → Trocq.Combinators{.Arrow,.Forall,.Universe} → Trocq.Solver`
(`Trocq.Lattice` is the single source of the class algebra; `lake build` builds the chain via `Trocq.lean`).

### Two boundary facts now *mechanically verified*
- Arrow/∀ at `≥2b` cost only **funext** (`[Quot.sound]`) — Lean has it → free.
- `Type` at `≥2b` costs **univalence** — Lean lacks it → universe combinator capped at `2a`,
  exactly as `requiresAxiom`/`depType` predict.

---

## What's next (toward a real tool)

Ordered roughly by leverage. The prototype is forward-compatible: each item extends, none rewrites.

1. **Full graded combinator family** *(arrow ✅, forall ✅, Type ✅, driver fully wired ✅, polymorphic
   binders ✅)* — arrow (≤(3,3)), dependent Π (≤(2b,2b)), universe (≤(2a,2a)) are all in place, and the
   driver assembles every former at its minimal per-node class, including under `∀ A:Type` binders.
   **Remaining:** (i) bound vars are currently supplied at the universe combinator's fixed inner class
   `(1,1)` (paramType's relation) — a use needing more than `(1,1)` would fail; lifting this needs the
   `Map_Type` sub-class table so the universe combinator's inner relation tracks the outer class. (ii)
   The deferred `(4,4)` coherence field `R_in_mapK` (the adjoint-equivalence triangle — Trocq's
   `Param44`, via half-adjoint machinery), which would lift arrow to `4` and Π past `2b`.

2. **User surface** — merge the `Solver` front half with a real `trocq` tactic **and** a `transfer%`
   term elaborator, on top of the graded combinators. Generalises `Tactic.lean` (single `∀` over a
   registered base) to arbitrary goals at *minimal* classes (weakest new goal).

3. **Registration** — `@[trocq]` attribute + environment extension, replacing the hardcoded
   `demoAtoms` / `buildCtx`. Stores `(B-type, witness, class)` per registered base/op.

4. **Mathlib reuse** — wire `Equiv` (registration menu), `Relator.LiftFun` (= `RArrow`), `Quot`
   (funext path) instead of bespoke definitions.

5. **Packaging** — ✅ done: lake project, `Trocq/` library, `Tests/` (`lake test`, green), `Examples/`
   demos. Still open: eventually fold the `Examples/` encodings onto the library so they stop
   duplicating it (they keep their own `mZero…` copies for now).

See `lean-port-design.md` §10 for the original phased plan.

---

## Quick build reference

```sh
lake build                              # build the whole Trocq library
lake test                               # run the test suite (fails on any regression)

lake env lean Examples/Driver.lean      # run a standalone (4,4) demo (Defeq/Minimal/Driver/Induction/Tactic)
```
