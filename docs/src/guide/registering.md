# Registering your own equivalence

Prove a witness and tag it `@[trocq]`; the driver reads it from the environment. Tagging classifies
the witness immediately (by the shape of its type, in `LeTrocq/Registry.lean`), so a malformed
witness is rejected right at the tag site. A witness is one of four **kinds**:

| Kind             | Type shape                                             | Registers                       |
|------------------|--------------------------------------------------------|---------------------------------|
| **base**         | `Param m n A B` (`A`, `B` closed consts)               | an equivalence of two types     |
| **relator**      | `∀ (m n : MapClass) …, Param m n (F …) (F' …)`          | an applied head `F` (graded)    |
| **type former**  | `∀ …, F args → F' args' → Sort`  (conclusion a `Sort`) | the parametricity *relation* of a parameterized type |
| **term primitive** | `∀ …, R … (c …) (c' …)`  (`R` a bare relation)        | a term head `c ↦ c'`            |

A proposition is just a `Sort 0` type, so a `Prop` predicate or logical connective registers as a
**relator** — there is no separate `Prop` machinery.

## A base equivalence

The recipe is: define the two types and their conversions, prove they form an equivalence, and tag
the `Param (4,4)` witness. From `Examples/NatUnary.lean`:

```lean
def RNU : Nat → Unary → Type := fun n u => PLift (u.toNat = n)

@[trocq] def RN : Param .map4 .map4 Nat Unary where
  R := RNU
  cov := { map := Unary.ofNat, map_in_R := …, R_in_map := …, R_in_mapK := fun _ _ _ => rfl }
  contra := { map := Unary.toNat, map_in_R := …, R_in_map := …, R_in_mapK := fun _ _ _ => rfl }
```

Register the equivalence at the **strong** class `(4,4)`. Each *use* is automatically weakened to the
minimal class it needs (see [Grading](../design/translation.md#sec-grading)), and the driver derives
the backward reading `Unary ≃ Nat` for free via `Param.sym`.

## Term primitives

To translate *terms* over the base, register each operation's relatedness. Its binders come in
abstraction-theorem **triples** `(a, a', aR)` — the `A`-value, the `B`-value, and their relatedness —
and its conclusion is a bare relation whose two sides name the heads `c ↦ c'`:

```lean
@[trocq] def R0 : RNU Nat.zero Unary.z := PLift.up rfl
@[trocq] def Rsucc (n : Nat) (u : Unary) (h : RNU n u) : RNU (Nat.succ n) (Unary.s u) := …
```

Registering a recursor primitive (`Nat.rec ↦ Unary.rec`) lets the translation cross recursion, so a
function defined by recursion transports to native recursion on the target side.

## Parameterized types: relators and type formers

A type *constructor* like `List : Type → Type` is a **relator**: its witness lifts a relation on
elements to a relation on lists, at **any** output class `(m, n)`, with the element built at the
minimal class a per-type variance table dictates (parallel to the arrow). It registers on both
surfaces:

- a **type former** (the inductive parametricity relation, e.g. `ListR`) so `⟨·⟩` / `[·]` can cross
  `List a`, plus the constructors as **term primitives**;
- the **graded relator** (e.g. `paramListRG m n`) for the `trocq` / `transfer%` path.

See `LeTrocq/ParamLib/List.lean` for the full pattern, `Sigma`/`Quot` for dependent families and a
`Prop`-relation argument, and `Examples/DepParam.lean` for a non-prelude dependent type (a W-tree).

## Propositions and predicates

A `Prop` predicate or connective is a graded relator concluding `Param m n (P …) (P' …)`; its
relation carries no data above class 1 (completeness is proof irrelevance). The connectives
`Not`/`And`/`Or`/`Iff` ship in `LeTrocq/ParamLib/Logic.lean`; a predicate example (`Pos`) is in
`Examples/NatUnary.lean`.

## Ground types need nothing

A type (or term) whose counterpart is *itself* is short-circuited to the generic diagonal witness
`paramRefl` (relation `PLift (a = b)`, identity maps) — so `Nat`, `Bool`, `Empty`, `Unit`, and any
composite built entirely from such parts transfer to themselves with **no registration**. A
registered equivalence overrides that diagonal whenever it applies.
