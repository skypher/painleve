# Quartic norm and first-zero identities

This note records identities used to attack positivity after the initial
coefficients.  They hold on any open \(a\)-interval on which the required
Gram matrices are nondegenerate.

Let \(P_n\) be the monic quartic orthogonal polynomials and normalize their
signed square norms by
\[
(P_n,P_n)=\rho(n)h_n,\qquad
\rho(n)=(-1)^n\prod_{j=0}^{n-1}\tau(j),
\]
where
\[
\tau(j)=
\begin{cases}
-1,&j\equiv3\pmod4,\\
1,&j\not\equiv3\pmod4.
\end{cases}
\]
Set
\[
V_n=\frac{h_{n+1}}{h_n},\qquad v_n=\frac{V_n}{a}.
\]

## Lemma 1 (norm derivative)

For \(n\geq3\),
\[
h_n'=-h_{n+1}+\frac1{a^2}\frac{h_n^2}{h_{n-3}}.
\]
For \(n=0,1,2\), the same formula holds with the second term omitted.

### Proof

The quartic multiplication formula is
\[
zP_n=P_{n+1}+\frac{\mathrm i}{a}\frac{h_n}{h_{n-3}}P_{n-3}.
\]
Differentiation of the pairing with respect to \(a\) gives
\[
\frac d{da}(P_n,P_n)=\tau(n)(zP_n,zP_n).
\]
The derivatives of the coefficients of \(P_n\) make no contribution because
\(\partial_aP_n\) has degree less than \(n\).

Orthogonality and the multiplication formula give
\[
(zP_n,zP_n)
=\rho(n+1)h_{n+1}
+\frac1{a^2}\rho(n-3)\frac{h_n^2}{h_{n-3}}.
\]
The sign definition implies
\[
\tau(n)\frac{\rho(n+1)}{\rho(n)}=-1,\qquad
\tau(n)\frac{\rho(n-3)}{\rho(n)}=1.
\]
Dividing by \(\rho(n)\) proves the identity. \(\square\)

## Corollary 2 (ratio differential equation)

For \(n\geq3\),
\[
V_n'
=-V_nV_{n+1}+V_n^2
+\frac1{a^2}V_nV_{n-1}V_{n-2}(V_n-V_{n-3}).
\]

### Proof

Lemma 1 gives
\[
\frac{h_n'}{h_n}
=-V_n+\frac1{a^2}V_{n-1}V_{n-2}V_{n-3}.
\]
Subtract this identity from the corresponding identity with \(n+1\) in
place of \(n\), then multiply by \(V_n\). \(\square\)

## Lemma 3 (elimination of the forward pole)

The recurrence at index \(n-1\) gives
\[
V_nV_{n+1}
=\frac{na}{V_{n-1}}-a^2-V_{n-2}V_{n-3}-V_nV_{n-2}.
\]
Equivalently,
\[
v_nv_{n+1}
=\frac{n\epsilon}{v_{n-1}}
-1-v_{n-2}v_{n-3}-v_nv_{n-2}.
\]

### Proof

Write the recurrence at \(n-1\) as
\[
V_{n-1}+\frac1{a^2}\left(
V_{n-1}V_{n-2}V_{n-3}
+V_nV_{n-1}V_{n-2}
+V_{n+1}V_nV_{n-1}\right)=\frac n a
\]
and solve for \(V_nV_{n+1}\). \(\square\)

## Proposition 4 (a sufficient first-zero exclusion)

Suppose \(n\geq3\), \(a_*>0\), and on an interval
\((a_*,a_*+\delta)\) one has
\[
V_{n-3},V_{n-2},V_{n-1},V_n>0,
\qquad \lim_{a\downarrow a_*}V_n(a)=0.
\]
Assume also that \(V_{n-3},V_{n-2},V_{n-1}\) extend continuously to
\(a_*\) with positive values there.
If
\[
V_n(a)V_{n+1}(a)\geq0
\]
on some right neighborhood of \(a_*\), then this configuration is
impossible.

### Proof

By Corollary 2,
\[
V_n'
=-V_nV_{n+1}+V_n^2
+\frac1{a^2}V_nV_{n-1}V_{n-2}(V_n-V_{n-3}).
\]
The last two terms have negative sum on a sufficiently small right
neighborhood of \(a_*\): after division by \(V_n>0\), they equal
\[
V_n+\frac1{a^2}V_{n-1}V_{n-2}(V_n-V_{n-3}),
\]
whose limit is strictly negative.  The first term is nonpositive by
hypothesis.  Hence \(V_n'<0\) on that neighborhood.

For \(a_*<a<b<a_*+\delta\), this gives \(V_n(b)<V_n(a)\).  Letting
\(a\downarrow a_*\) yields \(V_n(b)\leq0\), contradicting \(V_n(b)>0\).
\(\square\)

## Corollary 5 (the remaining supplier inequality)

At a hypothetical first zero as in Proposition 4, it is enough to prove
\[
\frac{na}{V_{n-1}}\geq a^2+V_{n-2}V_{n-3}+V_nV_{n-2}
\]
on a right neighborhood of \(a_*\).  In scaled variables this is
\[
\frac{n\epsilon}{v_{n-1}}
\geq1+v_{n-2}v_{n-3}+v_nv_{n-2}.
\]

By Lemma 3, this inequality is exactly
\(V_nV_{n+1}\geq0\).  Thus the positivity proof has been reduced locally to
a one-step adjacent-product sign estimate; no separate control of the
possible pole \(V_{n+1}\) is needed.

## Lemma 6 (explicit \(C_4\) block entries)

Let \(G\) be the monomial Gram matrix and fix a residue
\(r\in\{0,1,2,3\}\).  For \(p,q\geq0\), its \(r\)-block entry is
\[
G^{(r)}_{pq}
=(-1)^{r+q}\pi\,\mathrm i^{\,p-q}
\int_0^\infty
t^{r+2p+2q}e^{-at}J_{p-q}\left(\frac{t^2}{2}\right)\,dt.
\]

### Proof

Choose \(\eta=e^{\pi\mathrm i/4}\).  For
\(m=r+4q\), the twisting operator in the Hermitian pairing contributes
\((-1)^{r+q}\).  In polar coordinates, the angular integral is
\[
\int_0^{2\pi}e^{4\mathrm i(p-q)\theta}
\exp\left(\frac{\mathrm i}{2}R^4\cos4\theta\right)d\theta
=2\pi\mathrm i^{\,p-q}J_{p-q}\left(\frac{R^4}{2}\right).
\]
The substitution \(t=R^2\) gives the stated formula. \(\square\)

The next task is to extract Corollary 5 directly from either these block
integrals or a contiguous-minor identity.  A general determinant formula is
not required.
