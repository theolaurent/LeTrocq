# The graded parametricity translation

TODO intro text

## The classical (ungraded) translation

TODO
- quick presentation of the concept of parametricity
- presentation of vanilla parametricity translation in the context of the calculus of constructions


Ignoring grading, on the Calculus of Constructions the two translations are the standard binary
parametricity translation.

$$
\begin{array}{llcll}
  \Cpt{x}          &= x'                 &\qquad& \Rel{x}         &= x_R \\
  \Cpt{t\,u}       &= \Cpt{t}\,\Cpt{u}   &&      \Rel{t\,u}      &= \Rel{t}\; u\; \Cpt{u}\; \Rel{u} \\
  \Cpt{\lambda x{:}A.\,t} &= \lambda x'{:}\Cpt{A}.\,\Cpt{t} && \Rel{\lambda x{:}A.\,t} &= \lambda x\,x'\,x_R.\,\Rel{t} \\
  \Cpt{\Pi x{:}A.\,B}     &= \Pi x'{:}\Cpt{A}.\,\Cpt{B}     && \Rel{\Pi x{:}A.\,B} &= \Pi x\,x'\,x_R.\,\Rel{B} \\
  \Cpt{\square}    &= \square            &&      \Rel{\square}   &= \square \to \square \to \square
\end{array}
$$

