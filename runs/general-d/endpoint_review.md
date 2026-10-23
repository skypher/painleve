## Verdict: PASS WITH MINOR CHANGES

**Corollary 4.2 and its proof are correct.** There is one substantive but local correction in the Introduction: **the \(d=1\) norm ratios are \(V_n=(n+1)/a\), not \((n+1)a\)**. Your quotation faithfully reproduces the printed formula in Felder–Hoppe, but that formula contains an apparent reciprocal typo. The endpoint conclusion for \(d=1\) nevertheless follows from \(h(a)\to0\). The remaining changes concern specifying the endpoint prescription and saying “converges to a singular matrix.” [1]

### (a) Corollary 4.2: line-by-line verification

Write
\[
I_r(a)=\int_{\mathbb C}|z|^{2r}\rho_a\,dA,
\qquad
C_r=\text{the proposed positive limit constant}.
\]

**Conditioning identity.** For the unit-rate Gamma distribution used in the paper,
\[
\mathbb E[e^{-sG}]
=\frac1{\Gamma(\beta)}
 \int_0^\infty x^{\beta-1}e^{-(1+s)x}\,dx
=(1+s)^{-\beta}.
\]
Independence of \(G_{r,j_r}\) and \(R_r\) therefore gives exactly
\[
I_r(a)=\pi r!a^{-r-1}\mathbb E[(1+\kappa R_r)^{-\beta_r}].
\]

**Indices and exponents.** The omitted index is \(d-1-r\). For \(r\le d-2\), it is nonzero, so \(j_r=0\). For \(r=d-1\), it is zero, so \(j_r=1\). Consequently,
\[
d\beta_r=r+1+j_r,\qquad
\kappa^{\beta_r}
=d^{(d-2)\beta_r}a^{-r-1-j_r}.
\]
The displayed rescaling of \(a^{-j_r}I_r(a)\) is correct; no power of \(a\) or \(d\) is missing.

**Monotonicity and convergence.** For every \(R>0\),
\[
\frac{d}{d\kappa}\frac{\kappa}{1+\kappa R}
=\frac1{(1+\kappa R)^2}>0,
\qquad
\frac{\kappa}{1+\kappa R}\uparrow R^{-1}.
\]
Since \(\beta_r>0\), monotone convergence applies exactly as written. Moreover,
\[
\beta_{r,j}-\beta_r=\frac{j-j_r}{d}>0
\]
for every remaining factor. Independence and the Gamma negative-moment formula give
\[
\mathbb E[R_r^{-\beta_r}]
=\prod_{j\ne j_r}
 \frac{\Gamma(\beta_{r,j}-\beta_r)}{\Gamma(\beta_{r,j})}
\in(0,\infty).
\]
Thus finiteness is proved, not merely assumed.

**Empty product, \(d=2\).** Here \(R_r=1\) almost surely, and its negative moment and the Gamma product both equal \(1\). The argument remains valid without modification.

**Gram matrices and signs.** For \(N\le d-1\), distinct monomials have distinct residues modulo \(d\), so, for every \(a>0\),
\[
G_N(a)=\operatorname{diag}\bigl(I_0(a),-I_1(a),\ldots,(-1)^NI_N(a)\bigr).
\]
The limits are therefore nonsingular for \(N\le d-2\). For \(N=d-1\),
\[
G_{d-1}(a)\longrightarrow
\operatorname{diag}\bigl(C_0,-C_1,\ldots,(-1)^{d-2}C_{d-2},0\bigr),
\]
which has **rank exactly \(d-1\)**. Indeed, the proof establishes the stronger asymptotic
\[
\det G_{d-1}(a)
=(-1)^{d(d-1)/2}
 \left(\prod_{r=0}^{d-1}C_r\right)a\,(1+o(1)).
\]
All signs agree with `eq:gram-block`.

**Independent constants.** For \(d=2\), direct Gaussian integration and differentiation give
\[
I_0(a)=\frac{\pi}{\sqrt{1+a^2}},
\qquad
I_1(a)=\frac{\pi a}{(1+a^2)^{3/2}}.
\]
Hence \(C_0=C_1=\pi\), with the second limit understood as \(I_1(a)/a\to\pi\).

For \(d=3\), recomputation gives
\[
\begin{aligned}
C_0&=\pi\,3^{-1/3}\frac{\Gamma(1/3)}{\Gamma(2/3)}
     =4.30938913221948\ldots,\\
C_1&=\pi\,3^{1/3}\frac{\Gamma(2/3)}{\Gamma(1/3)}
     =2.29025601965218\ldots,\\
C_2&=2\pi\,3^{-4/3}\frac{\Gamma(1/3)}{\Gamma(5/3)}
     =C_0.
\end{aligned}
\]
These also follow independently from the expansion of Felder–Hoppe’s cubic Bessel formula: \(I_0=h\), \(I_1=-h'\), and their equation \(h''=ah+a^2h'\) gives \(I_2/a\to h(0)=C_0\). Thus the last number is the limit of **\(I_2/a\)**; \(I_2\) itself tends to zero. [1]

### (b) Norm ratios and the explicit cases

For \(d\ge2\) and \(0\le n\le d-1\), your identification is correct:
\[
P_n=z^n,\qquad
(P_n,P_n)_a=(-1)^nI_n(a),\qquad
\varrho(n)=(-1)^n,
\]
so \(\mathfrak h_n=I_n(a)\). In particular,
\[
V_{d-2}
=\frac{I_{d-1}(a)}{I_{d-2}(a)}
=\frac{C_{d-1}}{C_{d-2}}\,a(1+o(1))
\longrightarrow0.
\]
There is no missing sign.

The quoted **\(d=2\)** formulas are correct:
\[
h(a)=\frac{\pi}{\sqrt{1+a^2}},
\qquad
V_n=\frac{(n+1)a}{1+a^2}.
\]
They agree with the printed source. [1]

For **\(d=1\)**, the printed ratio formula is inconsistent with the stated definition \(V_n=h_{n+1}/h_n\). Using the source’s own polynomials \(P_n(z)=(z-i/a)^n\), direct Gaussian integration gives
\[
\int_{\mathbb C}
e^{s(z-i/a)+t(\bar z-i/a)}\rho_a(z)\,dA
=h(a)e^{st/a}.
\]
Accounting for the twist and signed-norm convention therefore yields
\[
h_n(a)=n!a^{-n}h(a),\qquad
\boxed{V_n(a)=\frac{n+1}{a}}.
\]
Thus these ratios diverge, rather than vanish. However,
\[
h(a)=\frac{\pi}{a}e^{-1/a}\longrightarrow0,
\]
so the **order-one Gram matrix already has a singular limit**. Use that fact instead of the erroneous ratio formula. The source prints both the stated \(h(a)\) and the shifted polynomials used in this calculation. [1]

### (c) Accuracy and fairness toward Felder–Hoppe

The paragraph correctly distinguishes their density’s domain \(a>0\), the conjecture’s printed \(a\ge0\), and the strictly positive parameter used in the proof of Theorem 3.7. That proof does not settle an independently defined endpoint problem. [1]

There is nevertheless a genuine qualification to make: **a literal endpoint reading of Theorem 3.7, using continuous Gram entries, is incompatible with these limits.** This does not undermine their positive-\(a\) result. Describe it as an endpoint/domain distinction, rather than a refutation of their theorem without qualification.

Their discussion of regularity at \(a=0\) is entirely compatible with your conclusion. In fact, their scalar equation
\[
(-1)^{d-1}h^{(d-1)}(a)=ah(a)+a^2h'(a)
\]
and regularity imply \(h^{(d-1)}(0)=0\). Analytic continuation of \(h\) does **not** imply nondegeneracy of the moment matrices. Your corollary supplies a direct moment-asymptotic proof and positive leading constants. Acknowledging this connection is appropriate. [1]

Replace “the natural one” by **“one natural prescription”**, explicitly identified as the entrywise Gaussian Abel limit. Also replace “becomes singular as \(a\to0^+\)” by **“converges to a singular matrix”**: the matrices remain nonsingular at every positive \(a\).

### (d) Other endpoint interpretations

The ordinary angular-first polar integral does **not** define the problematic entry. For the unsigned moment,
\[
I_{d-1}(0)\ \text{formally equals}\ 
\frac{\pi d}{2}\int_0^\infty sJ_0(s)\,ds,
\]
and
\[
\int_0^S sJ_0(s)\,ds=SJ_1(S)
=\sqrt{\frac{2S}{\pi}}\cos(S-3\pi/4)+O(S^{-1/2}).
\]
This has no limit. For the actual Gram entry, include the additional factor \((-1)^{d-1}\); it does not affect divergence. [2][3]

Other regularizations must be specified rather than silently identified with ordinary iterated integration. Analytic continuation of the fixed scalar function gives the same vanishing. Another natural prescription, exponential Abel damping in the polar variable, also gives zero:
\[
\int_0^\infty e^{-\varepsilon s}sJ_0(s)\,ds
=\frac{\varepsilon}{(1+\varepsilon^2)^{3/2}}
\longrightarrow0.
\]
This follows from the Bessel Laplace transform. [2]

There is also a useful structural obstruction. Put
\(\Phi=(z^d+\bar z^d)/d\). Any endpoint oscillatory prescription preserving integration by parts without boundary contributions must satisfy
\[
0=\operatorname{Os}\!\int_{\mathbb C}
 \partial_z\!\left(\bar z^q e^{i\Phi}\right)dA
=i\,\operatorname{Os}\!\int_{\mathbb C}
 z^{d-1}\bar z^q e^{i\Phi}\,dA.
\]
Hence \(z^{d-1}\) pairs to zero with every monomial, forcing degeneracy. A prescription producing a nonsingular endpoint matrix would therefore have to fail this identity, for example through retained boundary contributions. Such a prescription would not be the continuous extension considered here.

### Exact changes

**1. Replace the new Introduction paragraph with the following.** No change to Corollary 4.2 or its proof is needed.

:::writing{variant="document" id="60483" title="Replacement Introduction paragraph"}
The conjecture is stated for \(a\geq0\), whereas the density is
introduced for \(a>0\) \cite[Section~3.1]{FelderHoppe2025}, and the
proof of \cite[Theorem~3.7]{FelderHoppe2025} addresses strictly positive
\(a\). At \(a=0\) the planar moments are not absolutely convergent,
so an endpoint Gram matrix requires a prescription. One natural
prescription is the entrywise limit as \(a\to0^+\), or Gaussian Abel
regularization. Under this prescription, Corollary~\ref{cor:endpoint}
shows that, for every \(d\geq2\), the leading Gram matrix of order \(d\)
converges to a diagonal matrix of rank \(d-1\), and
\(V_{d-2}\to0\). The vanishing of the last diagonal entry is also
consistent with the differential equation for \(h\) and its regularity
at \(a=0\) discussed in \cite[equation~(3.5) and Section~4]{FelderHoppe2025}.
For \(d=1\), the explicit formula
\(h(a)=(\pi/a)\exp(-1/a)\) in \cite[Section~4]{FelderHoppe2025}
already shows that the Gram matrix of order one tends to zero.
Thus nondegeneracy does not extend to \(a=0\) under this prescription;
this endpoint distinction does not affect the positive-\(a\) cases
proved by Felder and Hoppe. We prove the conjecture for every \(a>0\).
:::

**2. Replace the new abstract sentence with:**

:::writing{variant="document" id="93176" title="Replacement abstract sentence"}
We also show that nondegeneracy does not extend continuously to
\(a=0\): for every \(d\geq2\), the leading Gram matrix of order \(d\)
converges, as \(a\to0^+\), to a matrix of rank \(d-1\).
:::

For a shorter Introduction, the \(d=1\) example can be omitted entirely; it is not needed for the \(d\ge2\) result.

Sources:
[1] https://sigma-journal.com/2025/103/sigma25-103.pdf
[2] DLMF: §10.22 Integrals ‣ Bessel and Hankel Functions ‣ Chapter 10 Bessel Functions — https://dlmf.nist.gov/10.22
[3] DLMF: §10.17 Asymptotic Expansions for Large Argument ‣ Bessel and Hankel Functions ‣ Chapter 10 Bessel Functions — https://dlmf.nist.gov/10.17

