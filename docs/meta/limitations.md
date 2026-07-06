# Limitations and future work

> **DISCLAIMER:** This page was written by an AI assistant and still needs human polishing and proof-reading.

*To be re-checked against the code before publishing — limitations move as the library grows.*

| limitation | where | why |
|---|---|---|
| `Type` above `(2a,2a)` fails | `mkUniv` | no univalence — completeness on `Type` is unprovable |
| `Eq` monomorphic at `Type` | `Lib/Eq.lean` | no `Sort`-polymorphic `Eq` witness yet |
| `Quot.lift` unsupported | `Lib/Quot.lean` | only the type former + `Quot.mk` are registered |
| recursor primitive monomorphic at `Type` | `Examples/NatUnary.lean` | no universe-polymorphic recursor witness yet |
| dependent family B-side may not depend on the element/proof | `assemble` app rule | throws "unsupported dependent family" |
| universe-polymorphic `Lib` deferred | `Lib/*` | polymorphic `ListR` etc. hits blockers |

Planned:

- an opt-in axiom layer lifting the `Type` cap (the `2b` / `3` / `4` `Type` arms) under univalence.
- universe-polymorphic relators and recursor primitives, removing the `Type`-monomorphic restrictions.
- further eliminators (`Quot.lift`) and element-dependent families.
- failure messages that name the stuck node and the demanded class.
