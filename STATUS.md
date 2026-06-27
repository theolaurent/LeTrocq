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
   The driver's `gen`/`assemble` now **do** handle dependent Π over a registered base (`piBase`) — `trocq`
   uses it for `∀ (x : Base), …` goals (item 2). Π over *`Type`* stays capped at `(2b,2b)` by the absent
   univalence (a true Lean boundary, not a gap).

2. **User surface** — ✅ **done** (`Trocq/Tactic.lean`): `transfer% T` elaborates to the witness
   `Param (4,4) T T'` (so `(transfer% (Nat→Nat)).cov.map` *is* the transported function, and it
   computes); `trocq` transfers the current goal to its counterpart and refines by the backward map.
   The driver's `gen`/`assemble` now handle **dependent Π over a registered base** (`∀ (x : Base), …`)
   and a **generic `app` node** (the abstraction-theorem rule `⟦head x⟧ = ⟦head⟧ x x' xR` for a
   registered constant `head`) — so `trocq` transfers real **`Prop` goals** end-to-end:
   `example : ∀ u : Unary, Pos u := by trocq; exact fun n => Nat.zero_le n` (reduces to `∀ n, Pos' n`).
   The `app` node now does **full argument transport**: a relator `head a₁ … aₙ` applied to *arbitrary*
   argument terms assembles via `⟦head⟧ a₁ a₁' a₁R … aₙ aₙ' aₙR`, where each `(aᵢ', aᵢR)` is produced by
   the **native term translation** (`Translate.param`) — so arguments may be multi-arg/curried
   (`app`-of-`app`), **nested applications** (`Pos (Unary.s u) ↦ Pos' (Nat.succ n)`), and **λ-abstractions**
   (`HOpred (fun u => u.s) ↦ HOpred' (fun n => n.succ)`), all in `Tests/Tactic.lean`. The backward direction
   the tactic runs in (goal-side → counterpart) is handled by a **bidirectional `Translate.buildCtx`**: every
   base is registered both ways (`Param.sym`) and every term primitive both ways (`Translate.symPrimitive`
   swaps the abstraction-theorem triples — the same proof serves both directions, only the value arguments
   swap position). Arguments that mention a bound **type** variable are handled too: the driver threads each
   `∀ A : Type`-bound variable into the argument-translation `env` (so a λ over `A` is rebuilt over the
   counterpart type). The `app` node reads each relator argument's shape (`relatorArgKinds`) to tell a TYPE
   arg (relatedness is a `Param m n`) from a TERM arg (a bare relation, built by the term translation). For a
   **TYPE arg the solver recursively builds its `Param`**: `gen` recurses to produce the argument's own
   sub-shape (forcing its class ≥ the relator's with a `Cstr.ge`), and `assemble` recursively assembles it —
   so a type argument may be a bare bound variable (`∀ A : Type, IdProp (fun a => a)`) OR a **compound type**
   over the bound variable (`IsInhab (fun (a : A) => a)`, where the relator's type parameter is `A → A`,
   built by `paramArrow`), and a registered base atom. Both transfer end-to-end (`Tests/Tactic.lean`).

3. **Registration** — ✅ **done** (`Trocq/Registry.lean` + `Trocq/Attr.lean`): `@[trocq]` attribute +
   env extension. Tagging a witness classifies it **eagerly** (`parseEntry`, run in the attribute's `add`)
   from its type into **base** (`Param m n A B`, both directions auto via `Param.sym`), **relator**
   (`∀…, Param … (P …)(P' …)`, keyed by head `P`), or **term primitive** (`∀…, R … (c …)(c' …)`, `c ↦ c'`),
   and stores the parsed `RegKind`. So a malformed witness is rejected right at the tag site
   (`@[trocq] def bogus : Nat := 5` ⤳ error there). Per-surface builders (`Solver.buildAtoms`/`buildConsts`,
   `Translate.buildCtx`) just read the stored entries; `transfer%`/`trocq`/`translate%` use them — nothing
   hardcoded. A predicate `@[trocq]`-registered in a *user* file is picked up by `trocq` with no library
   change (`Tests/Tactic.lean`). **Universe-polymorphic witnesses now register**: the env extension stores
   the witness *name* (not a level-baked `mkConst`), and every consumer rebuilds it with fresh universe
   levels (`mkConstWithFreshMVarLevels`) — needed for relators over a type variable (e.g. `IdPropR`), whose
   relation universe is a level parameter. Any residual free level (the universe combinator's relation
   level) is defaulted to 0 in `transfer`. *Open:* registering from a Mathlib `Equiv` (item 4).

4. **Mathlib reuse** — wire `Equiv` (registration menu), `Relator.LiftFun` (= `RArrow`), `Quot`
   (funext path) instead of bespoke definitions.

5. **Native term/program transport** — ✅ **done** (`Trocq/Translate.lean`): the full term-level
   parametricity translation `⟦·⟧`. For any term `t : T` the mutual `param`/`paramType` produce both the
   native counterpart `t'` (rebuilt over `B` leaf-by-leaf, *not* iso-conjugation) and the relatedness
   `tR : ⟦T⟧ t t'`. Structural over `.lam`/`.app`/`∀`(arrow+dependent Π)/`.sort`/`.fvar`; bottoms out at
   registered **primitives** and **unfolds** any other constant's definition (so `double` transports via
   `Nat.succ`/`Nat.zero` alone — item 1). `translate% t` ⤳ `t'`, `relate% t` ⤳ `tR`. Handles
   polymorphism (`fun (A:Type)(a:A) => a`). **`Nat` numeral leaves** are handled: a raw `.lit` or an
   `@OfNat.ofNat Nat …` numeral (even at an unreduced type like `motive 0`) is expanded to its `succ`/`zero`
   normal form and translated through the registered primitives (`translate% (2 : Nat) = Unary.s (Unary.s
   Unary.z)`). **Recursors transport**: a recursor is a registered term primitive (`Nat.rec ↦ Unary.rec`,
   witness `NatRecR` in `Examples/NatUnary.lean` — the eliminator's parametricity, proved by induction). The
   enabler is that `param` routes any **type-valued term** (the recursor's *motive* `M : Nat → Type`)
   through the type-level translation, so the motive is itself transported. A function defined by `Nat.rec`
   then transports to native `Unary` recursion and computes: `natDouble = Nat.rec 0 (·.succ.succ) ⤳ fun u =>
   Unary.rec Unary.z (·.s.s) u` (`Tests/Translate.lean`). *Open frontier:* **`match`-compiled defs** — a
   `match`/structural-recursion def goes through an auto-generated matcher (→ `Nat.casesOn`/`brecOn`), whose
   `Nat → Sort` motive type overflows `RArrow`'s universe (`⟦Sort⟧ = fun A B => A → B → Type` is `Type →
   Type → Type 1`); needs a universe-aware Π-over-`Sort` translation. Also: **universe-polymorphic** /
   **dependent-motive** recursor witnesses (`NatRecR` is monomorphic at `Type`), and non-`Nat` instance leaves.

See `lean-port-design.md` §10 for the original phased plan.

---

## Quick build reference

```sh
lake build    # build the whole Trocq library
lake test     # run the test suite (fails on any regression)
```
