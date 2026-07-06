
# Instructions for AI agents working on LeTrocq

## HARD RULE: never use side effects to dodge a language restriction

Do **not** use global mutable state (`IO.Ref`/`initialize`-set refs), `unsafe`/`implemented_by`, or elaboration side channels to work around mutual-recursion, import-cycle, or termination restrictions.

For genuine mutual recursion, use one of:
1. a real `mutual … end` block in one file, or
2. **dependency injection** — pass the capability as a function-valued parameter/record field, so the leaf module never imports the other.

Either way the dependency must be **explicit in a type signature**, never hidden behind a global side effect (which adds init-order coupling, hides the call graph, and turns a compile-time guarantee into a runtime one).

## HARD RULE: never use emojis

Do **not** use emojis anywhere — not in code, comments, documentation, commit messages, or chat responses.

## RULE: keep definitions universe-polymorphic

Don't hardcode a universe level (`Type`, `Sort 1`, `.{0}`, …) just to make something typecheck. Write definitions polymorphic over their universes (`Sort u` / auto-bound levels) so they apply at every level — unless the only consumers are inherently monomorphic. If a generic mechanism can't carry the level, fix the **mechanism**, not the definition.
