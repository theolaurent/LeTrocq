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

## Build / test

- `lake build` — warnings are errors.
- `lake test` — also runs the axiom-footprint guard (`LeTrocq.*` may use only `propext`/`Classical.choice`/
  `Quot.sound`; a stray `sorry` or new axiom fails the build). Don't weaken the guard to make something pass.
