# The Felder–Hoppe conjecture for every d (a > 0)

Status: candidate proof, awaiting independent review (2026-10-23).
Numerical checks: `runs/general-d/` (scripts and logs).

## Statement

Fix integers $d\ge2$ and a real $a>0$. Put
$$\rho_a(z)=\exp\Bigl(-a|z|^2+\tfrac{i}{d}(z^d+\bar z^d)\Bigr),$$
the density of Felder–Hoppe [FH, §3.1], with their Hermitian form
$(f,g)=\int_{\mathbb C} f\,\overline{\sigma g}\,\rho_a\,dA$, $\sigma f(z)=(-\eta)^{-\chi(\ell)}f(\eta z)$ on
the weight space $\mathbb C[z]_\ell$, $\eta^d=-1$, $\chi(\ell)=\ell$ for $0\le\ell\le d-1$
[FH, Prop. 3.1]. Let $\tau(\ell)=(-1)^{d-1}$ if $\ell\equiv-1 \bmod d$ and $\tau(\ell)=1$
otherwise, and $\varrho(n)=(-1)^n\prod_{\ell<n}\tau(\ell)$ [FH, Lemma 3.4, Example 3.5].

**Theorem A.** For every $d\ge2$ and $a>0$, every leading Gram matrix
$[(z^p,z^q)]_{p,q=0}^N$ is nondegenerate, and the signed norms $h_n$ defined by
$(P_n,P_n)=\varrho(n)h_n$ are all positive. Thus [FH, Conjecture 3.6] holds for all
$d$ and all $a>0$.

By [FH, §3.1, (3.1)–(3.3)], the ratios $V_n=h_{n+1}/h_n$ then form a positive solution of
$$V_n+\frac1{a^2}\sum_{j=0}^{d-2}\prod_{k=0}^{d-2}V_{n+j-k}=\frac{n+1}{a},$$
with $V_{-1}=\dots=0$ and the moment initial data $V_j=\int|z|^{2j+2}\rho_a/\int|z|^{2j}\rho_a$,
$0\le j\le d-3$. (The paper proves $d=4$; FH proved $d\le3$.)

Notation: $S_k=k(k-1)/2$; $\{{q\atop j}\}$ are Stirling numbers of the second kind;
$V(x_1,\dots,x_k)=\prod_{i<j}(x_j-x_i)$.

## 1. Blocks

For $m=\ell+dq$ with $0\le\ell\le d-1$: $\sigma z^m=(-\eta)^{-\ell}\eta^{\ell}(\eta^d)^q z^m=(-1)^{\ell+q}z^m$.
Since $\rho_a(\zeta z)=\rho_a(z)$ for $\zeta^d=1$, distinct weight spaces are orthogonal, and on
$\mathbb C[z]_r=\operatorname{span}\{z^{r+dq}\}$ the Gram matrix is
$$G^{(r)}_{pq}=(-1)^{r+q}M^{(r)}_{pq},\qquad M^{(r)}_{pq}=\int z^{r+dp}\bar z^{r+dq}\rho_a\,dA .$$
Let $\Delta^{(r)}_k=\det[G^{(r)}_{pq}]_{p,q<k}$. Exactly as in the paper (§2, Cor. 4.5): if all
$\Delta^{(r)}_k\neq0$, every leading Gram matrix is nondegenerate (it is block diagonal by
residue after a simultaneous permutation), monic orthogonal $P_n$ exist, $P_n\in\mathbb C[z]_{n\bmod d}$, and
for $n=r+dj$, $(P_n,P_n)=\Delta^{(r)}_{j+1}/\Delta^{(r)}_j$ (Schur complement). The number of
$\ell<n$ with $\ell\equiv d-1$ is $j$, so
$$\varrho(r+dj)=(-1)^{r+dj}\bigl((-1)^{d-1}\bigr)^j=(-1)^{r+j}.$$
Hence Theorem A follows from

**Proposition B.** $\operatorname{sgn}\Delta^{(r)}_k=(-1)^{rk+S_k}$ for all $0\le r\le d-1$, $k\ge1$.

Indeed then $\operatorname{sgn}(P_n,P_n)=(-1)^{r+(S_{j+1}-S_j)}=(-1)^{r+j}=\varrho(n)$.

## 2. Hankel reduction

For $\lambda>0$ let
$$W_r(\lambda)=\int_{\mathbb C}|z|^{2r}\exp\Bigl(-a|z|^2+\tfrac{i\lambda}{d}(z^d+\bar z^d)\Bigr)dA,\qquad F_r(t)=W_r(e^{t/2}).$$

**Lemma 1.** $\sum_{k\le p,\,l\le q}\{{p\atop k}\}\{{q\atop l}\}(i/d)^{k+l}M^{(r)}_{kl}=F_r^{(p+q)}(0)$ for all $p,q\ge0$, and
$$\Delta^{(r)}_k=(-1)^{rk}\,d^{2S_k}\det[F_r^{(p+q)}(0)]_{p,q<k}.$$

*Proof.* The first identity is the paper's Lemma 4.3 with 4 replaced by $d$, word for word:
on the disk $|z|\le R$ the two-source integral
$\mathcal Z_R(u,v)=\int_{|z|\le R}|z|^{2r}\exp(-a|z|^2+\frac id(uz^d+v\bar z^d))dA$ is entire;
the rotation $z\mapsto e^{i\varphi/d}z$ multiplies $z^d$ by $e^{i\varphi}$ and $\bar z^d$ by $e^{-i\varphi}$,
so $s\mapsto\mathcal Z_R(ue^s,ve^{-s})$ is constant and $\mathcal Z_R(e^{t_1},e^{t_2})=f_R(t_1+t_2)$;
the Stirling expansion $\frac{d^p}{dt^p}\exp(ce^t)=\sum_k\{{p\atop k}\}(ce^t)^k\exp(ce^t)$ gives the
truncated identity; and $R\to\infty$ is taken along real $t$, where the phase has modulus 1
and $t$-derivatives of order $m$ are bounded by $c_m(1+|z|)^{dm}$, so dominated convergence
applies. For the determinant, $G_{pq}=(-1)^{r+q}(d/i)^{p+q}[(i/d)^{p+q}M_{pq}]$; extracting
$(d/i)^p$ from rows and $(-1)^{r+q}(d/i)^q$ from columns gives the factor
$(-1)^{rk+S_k}(d/i)^{2S_k}=(-1)^{rk}d^{2S_k}$, and the Stirling matrices are unitriangular. ∎

(Checked numerically to $10^{-144}$ for $d=4,5,7$, all $r$, $k\le4$: `hankel_check.log`.)

So Proposition B is equivalent to $\operatorname{sgn}\det[F_r^{(p+q)}(0)]_{p,q<k}=(-1)^{S_k}$.

## 3. The kernels are Laplace transforms of products of Gamma variables

Let $J_r=\{0,1,\dots,d-1\}\setminus\{d-1-r\}$ and $\beta_j=(r+1+j)/d$ for $j\in J_r$
($d-1$ shapes, all in $(0,2)$). Let $G_j\sim\mathrm{Gamma}(\beta_j,1)$ be independent and
$S_r=\prod_{j\in J_r}G_j$.

**Lemma 2.** For $\lambda\ge0$,
$$W_r(\lambda)=\pi\,r!\,a^{-r-1}\,\mathbb E\Bigl[\exp\bigl(-\lambda^2 d^{\,d-2}a^{-d}S_r\bigr)\Bigr].$$

*Proof.* Scaling $z\mapsto a^{-1/2}z$ gives $W_r(\lambda;a)=a^{-r-1}W_r(\lambda a^{-d/2};1)$, so take $a=1$.

(i) Polar coordinates and $\int_0^{2\pi}e^{ix\cos(d\theta)}d\theta=2\pi J_0(x)$, then $u=R^2$:
$$W_r(\lambda)=\pi\int_0^\infty u^re^{-u}J_0\bigl(c\lambda u^{d/2}\bigr)du,\qquad c=2/d.$$

(ii) Mellin transform in $x=\lambda^2$. Fix $z$ with $0<\sigma=\operatorname{Re}z<\min(\tfrac14,\tfrac{r+1}d)$.
Since $|J_0(y)|\le\min(1,Cy^{-1/2})$, $\int_0^\infty y^{2\sigma-1}|J_0(y)|dy<\infty$, and the
substitution $y=c\sqrt x\,u^{d/2}$ gives
$\int_0^\infty x^{\sigma-1}|J_0(c\sqrt xu^{d/2})|dx=2(cu^{d/2})^{-2\sigma}\int y^{2\sigma-1}|J_0|dy$; as
$\int u^{r-d\sigma}e^{-u}du<\infty$, Fubini applies. With
$\int_0^\infty y^{2z-1}J_0(y)dy=2^{2z-1}\Gamma(z)/\Gamma(1-z)$ (DLMF 10.22.43),
$$\int_0^\infty x^{z-1}W_r(\sqrt x)\,dx=\pi\,d^{2z}\,\frac{\Gamma(z)\,\Gamma(r+1-dz)}{\Gamma(1-z)} .$$

(iii) Gauss's multiplication formula (DLMF 5.5.6) with $dw=r+1-dz$ gives
$\Gamma(r+1-dz)/\Gamma(r+1)=d^{-dz}\prod_{j=0}^{d-1}\Gamma(\beta_j-z)/\Gamma(\beta_j)$ with
$\beta_j=(r+1+j)/d$. The factor $j=d-1-r$ has $\beta_j=1$ and equals $\Gamma(1-z)$. Hence
$$\int_0^\infty x^{z-1}W_r(\sqrt x)\,dx=\pi\,r!\,\Gamma(z)\,(d^{\,d-2})^{-z}\prod_{j\in J_r}\frac{\Gamma(\beta_j-z)}{\Gamma(\beta_j)} .$$

(iv) The right side is the Mellin transform of
$x\mapsto\pi r!\,\mathbb E[\exp(-x\,d^{d-2}S_r)]$, by Tonelli and
$\mathbb E[G^{-z}]=\Gamma(\beta-z)/\Gamma(\beta)$, valid for $0<\sigma<\min_j\beta_j=(r+1)/d$.

(v) Both functions are continuous on $(0,\infty)$ and $x^{\sigma-1}f\in L^1$; equal Mellin
transforms on the line $\operatorname{Re}z=\sigma$ give equality (Fourier uniqueness). ∎

(Checked: exact agreement for $d=3$ to $10^{-22}$–$10^{-60}$; Monte Carlo for $d=4,\dots,8$,
all $r$, 90 cases, max $|z|$-score 2.0: `gamma_rep.log`.)

Consequently, with $\kappa=d^{d-2}a^{-d}$,
$$F_r(t)=\pi r!\,a^{-r-1}\,\mathbb E\bigl[\exp(-e^t\kappa S_r)\bigr].$$

## 4. The sign lemma

**Lemma 3.** Let $m\ge1$, $\beta_1,\dots,\beta_m>0$, $\kappa>0$, $G_j\sim\mathrm{Gamma}(\beta_j,1)$
independent, and $F(t)=\mathbb E[\exp(-e^t\kappa G_1\cdots G_m)]$. Then for all real $t$ and $k\ge1$,
$$(-1)^{S_k}\det[F^{(p+q)}(t)]_{p,q=0}^{k-1}>0 .$$

*Proof.* Let $X_j=\log G_j$, with density $q_j(v)=e^{\beta_jv-e^v}/\Gamma(\beta_j)$ on $\mathbb R$. Put
$\phi_0(u)=\exp(-e^u)$ and $\phi_j(u)=\mathbb E[\phi_{j-1}(u+X_j)]=\int\phi_{j-1}(w)\,q_j(w-u)\,dw$.
Then $F(t)=\phi_m(t+\log\kappa)$. Each $\phi_j$ is smooth with bounded derivatives and
$\phi_j^{(p)}(u)=\int\phi_{j-1}^{(p)}(w)q_j(w-u)dw$ (dominated convergence; $\phi_0^{(p)}$ is bounded).

*Claim.* For $u_1<\dots<u_k$: $(-1)^{S_k}\det[\phi_j^{(p)}(u_l)]_{p<k,\ l\le k}>0$.

Base $j=0$: with $x=e^u$, $\phi_0^{(p)}(u)=e^{-x}\sum_i\{{p\atop i}\}(-x)^i$ (paper eq. (stirling) with
$G(w)=e^{-w}$). The Stirling matrix is unitriangular, so
$\det[\phi_0^{(p)}(u_l)]=\prod_le^{-x_l}\,V(-x_1,\dots,-x_k)=(-1)^{S_k}\prod_le^{-x_l}V(x)$, and $V(x)>0$.

Step $j-1\to j$: by Andréief's identity (equivalently the basic composition formula),
$$\det[\phi_j^{(p)}(u_l)]=\int_{w_1<\dots<w_k}\det[\phi_{j-1}^{(p)}(w_i)]\;\det[q_j(w_i-u_l)]\prod dw_i .$$
Here $q_j(w-u)=\Gamma(\beta_j)^{-1}e^{\beta_jw}e^{-\beta_ju}\exp(\xi\eta)$ with $\xi=e^w$ and
$\eta=-e^{-u}$, both strictly increasing. The kernel $\exp(\xi\eta)$ is strictly totally
positive: $\det[e^{\xi_i\eta_l}]=\det[(e^{\xi_i})^{\eta_l}]>0$ for $\xi\uparrow,\eta\uparrow$ (generalized
Vandermonde determinant; e.g. Gantmacher–Krein, or Pólya–Szegő V.76, via Descartes'
rule of signs for $\sum c_le^{\eta_ly}$). So the second factor is positive on the ordered
region, the first has sign $(-1)^{S_k}$ by induction, and the claim follows.

Final step: write $u=t+\log\kappa$ and $H_{pq}=\phi_m^{(p+q)}(u)$. Differentiating
$\phi_m^{(p)}(u)=\int\phi_{m-1}^{(p)}(w)q_m(w-u)dw$ a further $q$ times in $u$ (allowed: see below),
$$H_{pq}=\int\phi_{m-1}^{(p)}(w)\,g_q(w)\,dw,\qquad g_q(w)=(-1)^q q_m^{(q)}(w-u).$$
From $q_m'=q_m(\beta_m-e^v)$, induction gives $q_m^{(q)}(v)=q_m(v)P_q(e^v)$ with $P_q$ of degree $q$
and leading coefficient $(-1)^q$ ($P_{q+1}(y)=(\beta_m-y)P_q(y)+yP_q'(y)$). So
$g_q(w)=q_m(w-u)\tilde P_q(e^{w-u})$ with $\tilde P_q$ monic of degree $q$, and
$|g_q|\le C_q q_m(w-u)(1+e^{w-u})^q$ is integrable locally uniformly in $u$, which justifies the
differentiation. Andréief's identity gives
$$\det H=\int_{w_1<\dots<w_k}\det[\phi_{m-1}^{(p)}(w_i)]\;\prod_i q_m(w_i-u)\;V\bigl(e^{w_1-u},\dots,e^{w_k-u}\bigr)\prod dw_i ,$$
where $V(e^{w_i-u})>0$ on the ordered region. By the claim, the integrand has sign
$(-1)^{S_k}$ and is nonzero on an open set. ∎

## 5. Proof of Proposition B and Theorem A

By Lemma 2, $F_r(t)=\pi r!a^{-r-1}\mathbb E[\exp(-e^t\kappa S_r)]$ with $m=d-1\ge1$ Gamma factors.
Lemma 3 gives $\operatorname{sgn}\det[F_r^{(p+q)}(0)]=(-1)^{S_k}$, and Lemma 1 gives
$\operatorname{sgn}\Delta^{(r)}_k=(-1)^{rk+S_k}$. Section 1 then gives Theorem A. ∎

## Remarks

1. **The case d = 4.** For $r=0$: $J_0=\{0,1,2\}$, shapes $\frac14,\frac12,\frac34$, and
   $G_{1/4}G_{3/4}\overset d=G_{1/2}'^2/4$ (duplication). This is the paper's
   $C\Phi_{0,0}(\lambda^2;a^2/2)$: one Gamma factor gives $(1+\lambda^2s^2)^{-1/2}$, and the other two
   give $e^{-ys}s^{-1/2}ds$. The paper's Lemma 3.1 is Lemma 3 with the last factor absorbed into
   $(1+ws^2)^{-b}$. The integration by parts for classes $r=2,3$ (Lemma 4.2) is not needed here.
   With $w=z^d$ instead of $z^2$, every class is handled at once. The Bessel identification
   (Section 5 of the paper) is needed only to write the $d=4$ initial data with Bessel functions.
2. **Explicit positive formula.** Unwinding Lemma 3 writes $(-1)^{rk+S_k}\Delta^{(r)}_k$ as a
   $k(d-1)$-fold integral of a positive function, as in the paper's Prop. 4.4.
3. **Uniqueness for d ≥ 5 is still open.** The analogue of Theorem 1.2 for $d\ge5$ is not
   proved. The a priori lower bound of Section 7 weakens to $v_n\ge c(n+1)^{-(d-3)}$, and the
   power-weight argument needs exponent at most 1. Local scans for $d=5,6$ support uniqueness.
4. **Recurrence.** [FH, §3.1] derive (3.1)–(3.3) for general $d$ "by the calculation of Theorem
   2.4", assuming the conjecture. A write-up should redo this derivation in the style of the
   paper's Section 6.

## References

[FH] G. Felder, J. Hoppe, Orthogonal polynomials with complex densities and quantum minimal
surfaces, SIGMA 21 (2025) 103, arXiv:2504.06197.
