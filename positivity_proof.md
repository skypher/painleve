# Positivity of the quartic solution

## Theorem

Let \(a>0\), put \(\epsilon=a^{-2}\), and set \(v_n=0\) for \(n<0\).
Let \(v_0,v_1\) be determined by
\[
v_0=-\frac1a\frac{h'(a)}{h(a)},\qquad
v_1=-\frac1a\frac{h''(a)}{h'(a)},
\]
where
\[
h(a)=\frac{\pi^2a}{4}\left[
J_{-1/4}\left(\frac{a^2}{4}\right)^2
-\sqrt2J_{-1/4}\left(\frac{a^2}{4}\right)
J_{1/4}\left(\frac{a^2}{4}\right)
+J_{1/4}\left(\frac{a^2}{4}\right)^2
\right].
\]
Then the sequence obtained from
\[
v_n\left(
1+v_{n-1}v_{n-2}+v_{n+1}v_{n-1}+v_{n+2}v_{n+1}
\right)=(n+1)a^{-2}
\tag{1}
\]
satisfies
\[
v_n(a)>0\qquad(n\geq0).
\]

The proof uses Gram determinants only as a sign device; no closed determinant
formula is needed.

## 1. A strictly sign-regular integral

For \(y>0\), \(\alpha\geq0\), and \(\beta\geq0\), define
\[
\Phi_{\alpha,\beta}(w;y)
=\int_0^\infty
e^{-ys}s^{\alpha-1/2}(1+ws^2)^{-\beta-1/2}\,ds,
\qquad w>0.
\tag{2}
\]
For \(p,q\geq0\), put
\[
D_{pq}^{\alpha,\beta}
=\left.
\partial_u^p\partial_v^q\Phi_{\alpha,\beta}(uv;y)
\right|_{u=v=1}.
\tag{3}
\]

### Lemma 1

For every \(k\geq1\),
\[
\mathop{\rm sign}\det
\left[D_{pq}^{\alpha,\beta}\right]_{p,q=0}^{k-1}
=(-1)^{k(k-1)/2}.
\tag{4}
\]
In particular, none of these determinants vanishes.

### Proof

Set
\[
b=\beta+\frac12,\qquad
\gamma=\frac{\alpha}{2}+\frac14,\qquad
L(y)=\Phi_{\alpha,\beta}(1;y).
\]
The substitution \(t=\sqrt w\,s\) in (2) gives
\[
\Phi_{\alpha,\beta}(w;y)
=w^{-\gamma}L\left(\frac{y}{\sqrt w}\right).
\tag{5}
\]
Let \(\vartheta=w\partial_w\), let
\((\vartheta)_{\underline p}=\vartheta(\vartheta-1)\cdots
(\vartheta-p+1)\), and set
\[
\mathcal A=-\gamma-\frac y2\partial_y.
\]
Ordinary derivatives of a function of \(uv\), followed by (5), give
\[
D_{pq}^{\alpha,\beta}
=
(\mathcal A)_{\underline p}(\mathcal A)_{\underline q}L(y).
\tag{6}
\]

Let
\[
f(s)=\frac{s^2}{1+s^2},\qquad
B_{pq}=\int_0^\infty
s^p f(s)^q e^{-ys}
s^{\alpha-1/2}(1+s^2)^{-\beta-1/2}\,ds.
\tag{7}
\]
Direct differentiation of (2) with respect to \(w\) yields
\[
(\mathcal A)_{\underline q}L(y)
=(-1)^q(b)_q B_{0q}.
\tag{8}
\]
On the other hand,
\[
(\mathcal A)_{\underline p}
=\sum_{i=0}^p c_{pi}(y)\partial_y^i,
\qquad
c_{pp}(y)=\left(-\frac y2\right)^p.
\tag{9}
\]
Since \(\partial_y^iB_{0q}=(-1)^iB_{iq}\), equations (6)--(9)
factor the matrix \(D=[D_{pq}^{\alpha,\beta}]\) as
\[
D=RBC,
\tag{10}
\]
where \(R\) is lower triangular with
\[
R_{pp}=\left(\frac y2\right)^p>0
\]
and \(C\) is diagonal with
\[
C_{qq}=(-1)^q(b)_q.
\]

It remains only to determine the sign of \(\det B\).  Andréief's identity
gives
\[
\det[B_{pq}]_{p,q=0}^{k-1}
=\frac1{k!}\int_{(0,\infty)^k}
\det[s_j^p]_{p,j=0}^{k-1}
\det[f(s_j)^q]_{q,j=0}^{k-1}
\prod_{j=1}^k d\mu(s_j),
\tag{11}
\]
where
\[
d\mu(s)=e^{-ys}s^{\alpha-1/2}
(1+s^2)^{-\beta-1/2}\,ds.
\]
Both determinants in (11) are Vandermonde determinants.  Their product is
nonnegative, because \(f(s)=s^2/(1+s^2)\) is strictly increasing, and is
strictly positive when the \(s_j\)'s are distinct.  Hence \(\det B>0\).
The diagonal of \(R\) is positive, while the sign of \(\det C\) is
\[
(-1)^{0+1+\cdots+(k-1)}=(-1)^{k(k-1)/2}.
\]
This proves (4). \(\square\)

## 2. The four quartic blocks

Write
\[
y=\frac{a^2}{2},\qquad C=\sqrt{\frac{\pi}{2}}.
\]
The connection formula
\[
J_{-1/4}(x)=\frac{J_{1/4}(x)-Y_{1/4}(x)}{\sqrt2}
\]
first rewrites the displayed Bessel expression in the theorem as
\[
h(a)=\frac{\pi^2a}{8}
\left(J_{1/4}\left(\frac{a^2}{4}\right)^2
+Y_{1/4}\left(\frac{a^2}{4}\right)^2\right).
\]
The Dixon--Ferrar integral
\[
J_\nu(x)^2+Y_\nu(x)^2
=\frac{8\cos(\pi\nu)}{\pi^2}
\int_0^\infty K_{2\nu}(2x\sinh t)\,dt,
\qquad |\mathop{\rm Re}\nu|<\frac12,
\]
together with
\[
K_{1/2}(x)=\sqrt{\frac{\pi}{2x}}e^{-x}
\]
and the substitution \(s=\sinh t\), therefore gives the positive
representation
\[
h(a)=C\int_0^\infty
\frac{e^{-ys}}{\sqrt{s(1+s^2)}}\,ds.
\tag{12}
\]

Introduce the angular source
\[
\mathcal Z(a;u,v)
=\pi\int_0^\infty e^{-at}
J_0\left(\frac{t^2\sqrt{uv}}2\right)\,dt.
\tag{13}
\]
This radial expression is the angularly integrated two-source function
with phase \(i(uz^4+v\bar z^4)/4\).  It is used only as a device for
generating moments at \(u=v=1\); no off-diagonal planar integral is
required.  Explicitly, termwise angular integration gives
\[
\int_0^{2\pi}
\exp\left(\frac{iR^4}{4}
(ue^{4i\theta}+ve^{-4i\theta})\right)d\theta
=2\pi J_0\left(\frac{R^4\sqrt{uv}}2\right),
\]
and \(t=R^2\) gives (13).
At \(u=v=1\), this is \(h(a)\).  Scaling \(t\) in (13), then using
(12), gives
\[
\mathcal Z(a;u,v)
=C\int_0^\infty
\frac{e^{-ys}}{\sqrt{s(1+uvs^2)}}\,ds
=C\Phi_{0,0}(uv;y).
\tag{14}
\]
Only derivatives at \(u=v=1\) will be used.

Put
\[
\mathcal Z_r=(-\partial_a)^r\mathcal Z,\qquad 0\leq r\leq3.
\]
Differentiating (14) gives the first two expressions below.  For the third,
an integration by parts in \(s\) gives
\[
y\int_0^\infty
\frac{e^{-ys}s^{3/2}}{\sqrt{1+uvs^2}}\,ds
=\frac12\int_0^\infty
\frac{e^{-ys}s^{1/2}}{\sqrt{1+uvs^2}}\,ds
+\int_0^\infty
\frac{e^{-ys}s^{1/2}}{(1+uvs^2)^{3/2}}\,ds.
\tag{15}
\]
Consequently,
\[
\begin{array}{c|c}
r&\mathcal Z_r\\ \hline
0&C\Phi_{0,0}(uv;y),\\[2mm]
1&aC\Phi_{1,0}(uv;y),\\[2mm]
2&2C\Phi_{1,1}(uv;y),\\[2mm]
3&2aC\Phi_{2,1}(uv;y).
\end{array}
\tag{16}
\]
Every scalar multiplier in (16) is positive.  Lemma 1 therefore implies
that, for
\[
D_{pq}^{(r)}
=\left.\partial_u^p\partial_v^q\mathcal Z_r(a;u,v)
\right|_{u=v=1},
\]
one has
\[
\mathop{\rm sign}\det[D_{pq}^{(r)}]_{p,q=0}^{k-1}
=(-1)^{k(k-1)/2}.
\tag{17}
\]

We now connect this sign to the quartic Gram form.  Its density is
\[
\exp\left(-a|z|^2+\frac i4(z^4+\bar z^4)\right),
\]
and its \(C_4\)-twist gives, in the residue class \(r\),
\[
G_{pq}^{(r)}
=(-1)^{r+q}
\int_{\mathbb C}
z^{r+4p}\bar z^{r+4q}
\exp\left(-a|z|^2+\frac i4(z^4+\bar z^4)\right)dA(z).
\tag{18}
\]
Indeed, if \(\eta=e^{\pi i/4}\) and \(m=r+4q\), the twisting operator
on \(z^m\) contributes
\[
(-\eta)^{-r}\eta^m=(-1)^{r+q}.
\]
Differentiating the angular integral that leads to (13) shows that
\[
G_{pq}^{(r)}
=(-1)^{r+q}
\left(\frac4i\right)^{p+q}D_{pq}^{(r)}.
\tag{19}
\]
All moment integrals in this differentiation are absolutely convergent.

Let
\[
\Delta_k^{(r)}
=\det[G_{pq}^{(r)}]_{p,q=0}^{k-1},
\qquad
S_k=\frac{k(k-1)}2.
\]
Set \(\Delta_0^{(r)}=1\).
Factoring the row and column phases in (19) makes them cancel:
\[
\Delta_k^{(r)}
=(-1)^{rk}16^{S_k}
\det[D_{pq}^{(r)}]_{p,q=0}^{k-1}.
\tag{20}
\]
It follows from (17) that
\[
\mathop{\rm sign}\Delta_k^{(r)}
=(-1)^{rk+S_k}.
\tag{21}
\]
In particular, every quartic block is nondegenerate.

## 3. Positive norms and the recurrence

The \(C_4\) symmetry makes distinct residue classes orthogonal.  If
\(n=r+4j\), Gram--Schmidt inside the \(r\)-th block therefore gives a
monic polynomial \(P_n\) with
\[
(P_n,P_n)=\frac{\Delta_{j+1}^{(r)}}{\Delta_j^{(r)}}.
\tag{22}
\]
Define
\[
\varrho(n)=(-1)^{n+\lfloor n/4\rfloor}.
\]
For \(n=r+4j\), this is \(\varrho(n)=(-1)^{r+j}\).  Taking the quotient
of the two signs in (21) gives
\[
\mathop{\rm sign}(P_n,P_n)
=(-1)^{r+j}=\varrho(n).
\tag{23}
\]
Thus the signed norms
\[
h_n=\varrho(n)(P_n,P_n)
\tag{24}
\]
are strictly positive for every \(n\geq0\).

Set
\[
V_n=\frac{h_{n+1}}{h_n},\qquad v_n=\frac{V_n}{a}.
\tag{25}
\]
Equation (24) immediately gives \(V_n>0\), hence
\[
v_n>0\qquad(n\geq0).
\tag{26}
\]

For completeness, let
\[
\tau(\ell)=
\begin{cases}
-1,&\ell\equiv3\pmod4,\\
1,&\ell\not\equiv3\pmod4.
\end{cases}
\]
Differentiating the density and integrating by parts gives
\[
\big((\partial_z+iz^3)f,g\big)
=-\tau(\ell)a(f,zg)
\tag{27}
\]
when \(g\) has \(C_4\)-weight \(\ell\).  The boundary term vanishes because
of the Gaussian factor.  Weight and degree considerations in (27) show that
\(zP_n\) can contain only \(P_{n+1}\) and \(P_{n-3}\), while
\((\partial_z+iz^3)P_n\) can contain only \(P_{n+3}\) and \(P_{n-1}\).
Pairing with the lower-degree term and using
\[
\varrho(n)=-\tau(n-1)\varrho(n-1),\qquad
\varrho(n)=\tau(n)\varrho(n-3),
\]
determines the coefficients:
\[
zP_n=P_{n+1}+\frac ia\frac{h_n}{h_{n-3}}P_{n-3},
\qquad
(\partial_z+iz^3)P_n
=iP_{n+3}+a\frac{h_n}{h_{n-1}}P_{n-1},
\tag{28}
\]
with terms having negative indices omitted.  In the coefficient of
\(P_{n-1}\) in \(z^3P_n\), the downward step in the first formula can
occur in any of three positions.  Since the coefficient of \(P_{n-1}\)
in \(\partial_zP_n\) is \(n\), (28) yields
\[
V_m\left[
1+\frac1{a^2}\left(
V_{m-1}V_{m-2}
+V_{m+1}V_{m-1}
+V_{m+2}V_{m+1}
\right)\right]
=\frac{m+1}{a}.
\tag{29}
\]
After \(V_m=av_m\), this is exactly (1).

Finally, \(P_0=1\), \(P_1=z\), and \(P_2=z^2\), so
\[
h_0=h,\qquad h_1=-h',\qquad h_2=h''.
\]
Consequently, (25) has precisely the prescribed initial values
\[
v_0=-\frac1a\frac{h'}h,\qquad
v_1=-\frac1a\frac{h''}{h'}.
\]
The forward form of (1) determines \(v_{n+2}\) from the preceding terms
whenever \(v_nv_{n+1}\neq0\).  Since the sequence constructed above is
strictly positive, induction identifies it with the sequence determined by
the stated initial values.  This proves the theorem. \(\square\)
