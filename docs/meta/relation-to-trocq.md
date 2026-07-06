# Relation to Trocq

> **DISCLAIMER:** This page was written by an AI assistant and still needs human polishing and proof-reading.

*Upstream: Cohen, Crance, Mahboubi, [Trocq: Proof Transfer for Free, With or Without
Univalence](https://arxiv.org/abs/2310.14022); implementation
[rocq-community/trocq](https://github.com/rocq-community/trocq).*

Shared with Trocq: the graded `(m,n)` annotations and the `MapClass` diamond, the per-former variance
tables (verbatim from `class.elpi`), and the twofold counterpart + relational-witness translation.

Lean-specific:

- **proof irrelevance** makes a class-4 relation a subsingleton, so the `(4,4)` coherence is free.
- **no univalence** caps `Type` at `(2a,2a)`, but `Prop` is uncapped (`propext` gives completeness) — the
  boundary lands inside Lean's own logic.
- **no fixpoint** — bound variables pinned at inner `(4,4)`, one top-down sweep, replacing annotation
  inference by constraint solving.
- **no elpi** — grading is inline in `MetaM`; the relator database is a plain environment extension.

| Trocq | LeTrocq |
|---|---|
| annotation `(α, β)` | `Param m n` / `ParamClass` |
| `class.elpi` order / join | `MapClass.le` / `join` / `meet` |
| `Map_Type` / `Param_Type` | `paramTypeAt` (capped `2a`), `paramProp` (`4`) |
| weakening | `MapClass.weaken` / `Param.weaken` |
| annotation inference (constraint solving) | demand-driven `assemble`, bound vars pinned `(4,4)` |
| relator database (elpi) | `@[trocq]` environment extension |
