

# Parametricity Translation

The parametricity translation is a twofold translation consisting of a simple term translation ⟨.⟩ and a relational translation [.] with the invariant t : A implies [t] : [A] t ⟨t⟩.

On the calculus of construction, it is defined as follows

⟨x⟩ := x'
⟨t u⟩ := ⟨t⟩ ⟨u⟩
⟨λx:A. t⟩ := λx':⟨A⟩. ⟨t⟩
⟨Πx:A. B⟩ := Πx':⟨A⟩. ⟨B⟩
⟨□⟩ := □

[x] := xR
[t u] := [t] u ⟨u⟩ [u]
[λx:A. t] := λx:A x':⟨A⟩ xR:[A]. [t]
[Πx:A. B] := Πx:A x':⟨A⟩ xR:[A]. [B]
[□] := □ → □ → □

When the relation need to carry additional proof information, there is a need for a type-level and a term level translation.

[x] := xR
[t u] := [t] u ⟨u⟩ [u]
[λx:A. t] := λx:A x':⟨A⟩ xR:〚A〛. [t]
[Πx:A. B] := { R:= Πx:A x':⟨A⟩ xR:〚A〛. 〚B〛 ; ... }
[□] := { R:= □ → □ → □ ; ... }

〚A〛 := A.R

Here the translation is *graded* with a tuple (map, map') indicating the strength of the relation.

The grading is provided by a dedicated solver which solves constraints with regard to type dependency.
For instance [Πx:A. B]@(0, 1) := { R: Πx:A x':⟨A⟩ xR:〚A〛@(2a, 0). 〚B〛@(0, 1) ; ... }
