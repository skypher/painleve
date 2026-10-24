CONFIRMED.

Nonnegativity gives both upper bounds, since \(v_n\) and \(T_n\) occur in the \(n\)-th equation. Terms with \(m<0\) vanish by definition. Every remaining window contains \(n\), and there are exactly \(\min(n+1,d-1)\) such windows. After factoring out \(v_n\), each product has \(d-2\) factors with nonnegative indices satisfying
\[
i+1\le n+d-1\le(d-1)(n+1).
\]
Thus the factor estimates are valid, including the boundary windows at \(n=0\) and the case \(d=3\).

Writing \(B_n\) for the bracket, the displayed estimate correctly gives
\[
1\le B_n\le K(n+1)^{d-2},
\]
using \((n+1)^{d-2}\ge1\). The final division therefore has the correct inequality direction:
\[
v_n=\frac{(n+1)\epsilon}{B_n}
\ge\frac{(n+1)\epsilon}{K(n+1)^{d-2}}
=\frac{\epsilon}{K}(n+1)^{-(d-3)}.
\]

The supplied diff changes only the proof paragraph implementing R1. The lemma’s statement, \(K\), and all other text are unchanged in that diff. No replacement text is needed.
