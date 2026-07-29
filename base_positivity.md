# Positivity of the first three coefficients

Throughout, let
\[
x=\frac{a^2}{4},\qquad \nu=\frac14,\qquad
M_\nu(x)=J_\nu(x)^2+Y_\nu(x)^2.
\]

## Lemma 1 (Bessel amplitude form)

For every \(a>0\),
\[
h(a)=\frac{\pi^2a}{8}M_{1/4}\left(\frac{a^2}{4}\right).
\]

### Proof

For nonintegral \(\nu\),
\[
J_{-\nu}(x)=\cos(\pi\nu)J_\nu(x)-\sin(\pi\nu)Y_\nu(x).
\]
At \(\nu=1/4\), if \(J=J_{1/4}(x)\) and \(Y=Y_{1/4}(x)\), this gives
\[
J_{-1/4}(x)=\frac{J-Y}{\sqrt2}.
\]
Consequently,
\[
J_{-1/4}^2-\sqrt2J_{-1/4}J_{1/4}+J_{1/4}^2
=\frac12(J^2+Y^2).
\]
Substitution in the defining formula for \(h\) proves the claim. \(\square\)

## Lemma 2 (monotonicity of the quartic Bessel amplitude)

The function
\[
F(x)=xM_{1/4}(x)
\]
is strictly increasing on \((0,\infty)\).

### Proof

Nicholson's integral (Gradshteyn--Ryzhik 6.664.4) gives, for \(x>0\),
\[
M_\nu(x)=\frac8{\pi^2}\int_0^\infty
K_0(2x\sinh t)\cosh(2\nu t)\,dt.
\]
The integral and its first \(x\)-derivative converge locally uniformly for
\(x>0\).  Indeed, near \(t=0\), \(K_0(2x\sinh t)=O(1+|\log t|)\) and
\(\sinh(t)K_1(2x\sinh t)=O(1)\); as \(t\to\infty\), both terms decay
superexponentially after multiplication by \(\cosh(2\nu t)\).

Put \(z=2x\sinh t\) and \(w(t)=\cosh(2\nu t)\).  Since
\[
\partial_tK_0(z)=-2x\cosh(t)K_1(z),
\]
we have
\[
zK_1(z)=-\tanh(t)\,\partial_tK_0(z).
\]
Differentiating \(xM_\nu(x)\), then integrating by parts in \(t\), gives
\[
\begin{aligned}
\frac{\pi^2}{8}\frac{d}{dx}\bigl(xM_\nu(x)\bigr)
&=\int_0^\infty w(t)\bigl(K_0(z)-zK_1(z)\bigr)\,dt\\
&=\int_0^\infty K_0(z)w(t)\tanh(t)
 \left(\tanh(t)-2\nu\tanh(2\nu t)\right)\,dt.
\end{aligned}
\]
The boundary term vanishes: at \(t=0\), \(\tanh(t)K_0(2x\sinh t)\to0\);
at infinity, \(K_0(2x\sinh t)\) decays superexponentially.

For \(\nu=1/4\) and \(t>0\),
\[
\tanh t-\frac12\tanh\frac t2>0.
\]
All the other factors in the last integral are positive.  Hence
\(F'(x)>0\). \(\square\)

## Proposition 3 (four signs of \(h\))

For every \(a>0\),
\[
h(a)>0,\qquad h'(a)<0,\qquad h''(a)>0,\qquad
h(a)+ah'(a)>0.
\]

### Proof

Lemma 1 and \(J_\nu^2+Y_\nu^2>0\) give \(h>0\).  (The Wronskian
\(J_\nu Y_\nu'-J_\nu'Y_\nu=2/(\pi x)\) excludes a common zero.)

By Lemma 1,
\[
ah(a)=\frac{\pi^2}{2}F\left(\frac{a^2}{4}\right).
\]
Lemma 2 therefore gives
\[
h(a)+ah'(a)=\frac{d}{da}(ah(a))>0.
\]

The differential equation for the quartic initial-value function is
\[
h'''(a)+ah(a)+a^2h'(a)=0.
\]
Thus
\[
h'''(a)=-a\bigl(h(a)+ah'(a)\bigr)<0.
\]
It follows that \(h''\) is strictly decreasing.  If \(h''(a_0)\leq0\) at
some \(a_0>0\), then \(h''\) is bounded above by a negative constant on a
tail, forcing \(h\) eventually to become negative.  Hence \(h''>0\).

Now \(h'\) is strictly increasing.  The integral representation defining
\(h\), after the Gaussian rescaling \(z\mapsto a^{-1/2}z\), gives
\(\lim_{a\to\infty}ah(a)=\pi\), so \(h(a)\to0\).  If \(h'(a_0)\geq0\),
then strict increase would make \(h\) increase on a tail, contradicting
\(h(a)\to0\).  Therefore \(h'<0\). \(\square\)

## Corollary 4 (positivity through \(n=2\))

Let
\[
v_0=-\frac1a\frac{h'}h,\qquad
v_1=-\frac1a\frac{h''}{h'},\qquad \epsilon=a^{-2}.
\]
Then, for every \(a>0\),
\[
0<v_0<\epsilon,\qquad v_1>0,\qquad v_2>0.
\]

### Proof

The signs of \(v_0\) and \(v_1\) follow from Proposition 3.  Moreover,
\[
v_0<\epsilon
\quad\Longleftrightarrow\quad
-\frac{h'}{ah}<\frac1{a^2}
\quad\Longleftrightarrow\quad
h+ah'>0.
\]
At \(n=0\), the recurrence is
\[
v_0(1+v_1v_2)=\epsilon.
\]
Therefore
\[
v_2=\frac{\epsilon/v_0-1}{v_1}>0.
\]
\(\square\)

## Lemma 5 (positive Laplace representation)

For \(a>0\),
\[
h(a)=\sqrt{\frac{\pi}{2}}\int_0^\infty
\frac{e^{-a^2s/2}}{\sqrt{s(1+s^2)}}\,ds.
\]

### Proof

The second form of Nicholson's integral, valid for
\(|\mathop{\rm Re}\nu|<1/2\) and \(x>0\), is
\[
J_\nu(x)^2+Y_\nu(x)^2
=\frac{8\cos(\pi\nu)}{\pi^2}
\int_0^\infty K_{2\nu}(2x\sinh t)\,dt.
\]
At \(\nu=1/4\), use
\[
K_{1/2}(u)=\sqrt{\frac{\pi}{2u}}e^{-u}
\]
in Lemma 1, and then set \(s=\sinh t\).  Since \(2x=a^2/2\),
the constants simplify to the claimed formula. \(\square\)

## Lemma 6 (a strict covariance inequality)

Set
\[
y=\frac{a^2}{2},\qquad
q(a)=-a\frac{h'(a)}{h(a)}.
\]
Then \(q'(a)>0\) for every \(a>0\).

### Proof

Let \(\mathbb P_y\) be the probability measure on \((0,\infty)\) whose
unnormalized density is
\[
e^{-ys}w(s),\qquad
w(s)=\frac1{\sqrt{s(1+s^2)}}.
\]
Write \(m=\mathbb E_y[s]\) and
\(\operatorname{Var}_y(s)=\mathbb E_y[s^2]-m^2\).  Lemma 5 gives
\[
q=2ym,\qquad
\frac{dq}{dy}=2\left(m-y\operatorname{Var}_y(s)\right).
\]

Put \(f(s)=s^2/(1+s^2)\).  Since
\[
\frac{w'(s)}{w(s)}=-\frac1{2s}-\frac{s}{1+s^2},
\]
integration of the derivatives of
\(s w(s)e^{-ys}\) and \(s^2w(s)e^{-ys}\) gives
\[
ym=\frac12-\mathbb E_y[f(s)],
\qquad
y\mathbb E_y[s^2]=\frac32m-\mathbb E_y[sf(s)].
\]
The boundary terms vanish at both endpoints.  Substitution yields
\[
m-y\operatorname{Var}_y(s)
=\mathbb E_y[sf(s)]-\mathbb E_y[s]\mathbb E_y[f(s)]
=\operatorname{Cov}_y(s,f(s)).
\]
Both \(s\) and \(f(s)\) are strictly increasing, and \(\mathbb P_y\) is
not concentrated at one point.  Equivalently, using two independent
copies \(S,T\),
\[
2\operatorname{Cov}_y(s,f(s))
=\mathbb E_y[(S-T)(f(S)-f(T))]>0.
\]
Thus \(dq/dy>0\), and \(q'(a)=a\,dq/dy>0\). \(\square\)

## Proposition 7 (positivity through \(n=3\))

For every \(a>0\), one has \(v_3(a)>0\).

### Proof

Let \(h_0=h\), \(h_1=-h'\), \(h_2=h''\), and \(h_3=-h'''\).  The
quartic differential equation and the definition of \(q\) give
\[
h_3=a(h+ah')=ah(1-q).
\]
The norm derivative identity at \(n=3\) is
\[
h_3'=-h_4+\frac1{a^2}\frac{h_3^2}{h_0}.
\]
Differentiating \(h_3=ah(1-q)\) and substituting into this identity gives
the exact cancellation
\[
h_4=ah\,q'(a).
\]
Lemma 6 therefore gives \(h_4>0\).  Since
\[
v_3=\frac1a\frac{h_4}{h_3}
\]
and Proposition 3 gives \(h_3=-h'''>0\), it follows that \(v_3>0\).
\(\square\)
