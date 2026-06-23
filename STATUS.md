# TROCQ2LEAN — Status & Next Steps

Porting [Trocq](https://arxiv.org/abs/2310.14022) (modular parametricity / proof transfer) to Lean 4
as a Lean-native reformulation. This is a **research prototype**: a Lean-native reformulation (not a
1:1 port), staged so the small `(4,4)` examples are a forward-compatible first rung of the full graded
lattice — extending additively, no rewrite.

See `lean-port-design.md` for the full design rationale. This file is the live status.

- **Toolchain:** `leanprover/lean4:v4.26.0-rc2` (elan).
- **Prototype lives in:** `lean-proto/` (no lakefile yet — files compiled standalone).
- **Everything below compiles**; axiom footprint is tracked per file (goal: nothing beyond
  `Quot.sound`, which underlies `funext` and is a kernel rule, not an added axiom).

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

### Foundations (fixed-class `(4,4)` artifacts)

| File | What it establishes | Axioms |
|---|---|---|
| `Defeq.lean` | The **encoding**: 6 graded `MapKHas` structs + indexed `MapHas` (ULift on small levels) + `Param m n A B`. Answers open-q #4: abstraction-theorem defeq holds by `rfl`; projections compute. | — |
| `Minimal.lean` | Hand-written transfer: registers `Nat ≃ Unary` as a `(4,4)` witness `RN`; a generic `transfer_induction` derives `Unary.induction` **for free** from `Nat.rec`. | none |
| `Driver.lean` | Term-first **parametricity-translation driver** (metaprogram over `Expr`). Generates native `f.B := fun u => u.s.s` + `Param` proof from `f := fun n => n.succ.succ`. | none |
| `Induction.lean` | Driver extended to **higher-order / dependent** terms (sorts, dependent `Π`, applied predicates). Generates the `Unary` induction principle. | none |
| `Tactic.lean` | The first **`trocq` tactic**: `by trocq` transfers a `Unary` goal to the (easier) `Nat` goal via the comap direction. | none |

### Milestone 6 — the full graded lattice (4 layers)

| Layer | File | What it adds | Axioms |
|---|---|---|---|
| 1 | `Lattice.lean` | The **class algebra**: `MapClass` lattice (`le`/`join`/`meet`), `ParamClass` ops, dependency tables (`depPi`/`depArrow`/`depType`), and the **monotone least-fixpoint solver** (`Cstr` + `solve`). Validated against the paper's tables by `rfl`. | — (pure) |
| 2 | `Hierarchy.lean` | The witness side + **weakening** (the ⇓ forget maps): six covering-edge projections composed into `MapClass.weaken : tgt ≤ src → MapHas src → MapHas tgt`, lifted to `Param.weaken` + named downgrades (`toRetraction`/`toSection`/`toFunction`/`toRel`). | none |
| 3 | `Combinators.lean` | The proof-heavy **combinators**: `paramArrow33` (arrow at (3,3), completeness via funext), `paramArrowLow` (same former at minimal class (0,1) — **zero proofs**), `paramType` (universe combinator at the **no-univalence ceiling** (2a,2a)). | `paramArrow33`: `[Quot.sound]` (=funext); `paramType`: **none** |
| 4 | `Solver.lean` | **The driver, wired.** Front half: walk an `Expr`, emit `Cstr`, run the real `solve` → minimal class per occurrence (reproduces the paper's `∀A:Type,A→A` ⇒ Type→(2a,0), A→(1,1), *from the Expr*). Back half: assemble the witness via `paramArrow33` + `weaken`. | generated witness: `[Quot.sound]` |

**Module dependency chain:** `Lattice → Hierarchy → Combinators → Solver`
(`Lattice` is the single source of the class algebra; build oleans in that order with
`LEAN_PATH=".:$(lake env printenv LEAN_PATH)"`).

### Two boundary facts now *mechanically verified*
- Arrow/∀ at `≥2b` cost only **funext** (`[Quot.sound]`) — Lean has it → free.
- `Type` at `≥2b` costs **univalence** — Lean lacks it → universe combinator capped at `2a`,
  exactly as `requiresAxiom`/`depType` predict.

---

## What's next (toward a real tool)

Ordered roughly by leverage. The prototype is forward-compatible: each item extends, none rewrites.

1. **Full graded combinator family** *(biggest piece)* — `Combinators.lean` has two representative
   arrow combinators + one universe combinator. The real tool needs `param_arrow` / `param_forall` /
   `param_Type` at **all** classes, including the `(4,4)` coherence field `R_in_mapK` (the
   adjoint-equivalence triangle — Trocq's `Param44`, via half-adjoint machinery). This is what lets the
   driver's **back half consume the per-node minimal classes** (cheapest combinator per node) and handle
   **polymorphic binders**. *The front half (`Solver.lean`) already computes those classes correctly.*

2. **User surface** — merge the `Solver` front half with a real `trocq` tactic **and** a `transfer%`
   term elaborator, on top of the graded combinators. Generalises `Tactic.lean` (single `∀` over a
   registered base) to arbitrary goals at *minimal* classes (weakest new goal).

3. **Registration** — `@[trocq]` attribute + environment extension, replacing the hardcoded
   `demoAtoms` / `buildCtx`. Stores `(B-type, witness, class)` per registered base/op.

4. **Mathlib reuse** — wire `Equiv` (registration menu), `Relator.LiftFun` (= `RArrow`), `Quot`
   (funext path) instead of bespoke definitions.

5. **Packaging** — turn `lean-proto/` into a proper lake project; merge the consolidated
   `Lattice/Hierarchy/Combinators/Solver` into a library; retire the standalone `(4,4)` artifacts
   (`Defeq`/`Minimal`/`Driver`/`Induction`/`Tactic`) into `examples/` or tests.

See `lean-port-design.md` §10 for the original phased plan.

---

## Quick build reference

```sh
cd lean-proto
LP=".:$(lake env printenv LEAN_PATH)"
lake env lean -o Lattice.olean    Lattice.lean
LEAN_PATH="$LP" lake env lean -o Hierarchy.olean   Hierarchy.lean
LEAN_PATH="$LP" lake env lean -o Combinators.olean Combinators.lean
LEAN_PATH="$LP" lake env lean      Solver.lean      # runs the demos
```

The standalone `(4,4)` files (`Defeq` / `Minimal` / `Driver` / `Induction` / `Tactic`) each compile on
their own with plain `lake env lean <File>.lean`.
