# Instructions for AI agents working on LeTrocq

## HARD RULE: never use side effects to dodge a language restriction

Do **not** use global mutable state (`IO.Ref`/`initialize`-set refs), `unsafe`/`implemented_by`, or
elaboration side channels to work around mutual-recursion, import-cycle, or termination restrictions.

For genuine mutual recursion, use one of:
1. a real `mutual … end` block in one file, or
2. **dependency injection** — pass the capability as a function-valued parameter/record field, so the leaf
   module never imports the other.

Either way the dependency must be **explicit in a type signature**, never hidden behind a global side effect
(which adds init-order coupling, hides the call graph, and turns a compile-time guarantee into a runtime one).

## RULE: keep definitions universe-polymorphic

Don't hardcode a universe level (`Type`, `Sort 1`, `.{0}`, `PUnit.{1}`, …) just to make something typecheck.
Write definitions polymorphic over their universes (`Sort u` / auto-bound levels) so they apply at every
level. If a generic mechanism can't carry the level (e.g. the translation reusing an occurrence's universe),
fix the **mechanism**, not the definition. Precedent: `LeTrocq.ParamLib.Unit`'s `UnitRel`/`UnitR` are universe-
polymorphic; the driver reuses the occurrence's levels for homogeneous formers (`relevelHomogeneous` in
`LeTrocq/Translate.lean`) rather than pinning `PUnit` at a fixed universe.

## Build / test

- `lake build` — warnings are errors.
- `lake test` — also runs the axiom-footprint guard. EVERY `LeTrocq.*` decl is checked, so a stray `sorry`
  or new axiom always fails the build; only the tolerated standard axioms differ by layer. OBJECT-LEVEL
  `LeTrocq.*` (combinators, witnesses, registered bases, and every `Param` the driver GENERATES) may use only
  `propext`/`Quot.sound` — no `Classical.choice`. The metaprogram modules (`Registry`/`Attr`/`Translate`/
  `Solver`/`Tactic`) additionally tolerate `Classical.choice`: they run on `MetaM`, whose root API
  (`Lean.Meta.inferType`, …) uses choice like every Lean tactic — compile-time tooling that never enters a
  generated proof. Don't weaken the guard (don't broaden an axiom set, don't move object-level code into a
  metaprogram module) to make something pass.
