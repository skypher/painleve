#!/usr/bin/env python3
"""Signed norms of the Felder-Hoppe form for general d (Conjecture 3.6 test).

Usage: python3 -u gram.py [-h|--help] d a N [dps]

Density rho_a(z) = exp(-a|z|^2 + (i/d)(z^d + zbar^d)).  Moments
M_pq^(r) = int z^{r+dp} zbar^{r+dq} rho_a dA = 2 pi i^n I(K, n), with
n = |p-q|, K = 2r + d(p+q) + 1 and I(K,n) = int_0^oo R^K e^{-aR^2}
J_n(2R^d/d) dR, computed as the power series in a whose coefficients are
the Mellin moments int x^mu J_n(x) dx = 2^mu Gamma((n+mu+1)/2) /
Gamma((n-mu+1)/2).  Gram blocks G_pq = (-1)^{r+q} M_pq, norms
(P_n,P_n) = Delta_{j+1}/Delta_j (n = r + dj), signed norms
h_n = rho(n) (P_n,P_n) with rho(n) = (-1)^n prod_{l<n} tau(l),
tau(l) = (-1)^{d-1} if l = -1 mod d, else 1.  Prints h_n, its sign, and
the residual of the recurrence (3.3) of Felder-Hoppe for V_n = h_{n+1}/h_n.
"""
import sys
if any(x in ("-h", "--help") for x in sys.argv[1:]) or len(sys.argv) < 4:
    print(__doc__); sys.exit(0)
import time
import mpmath as mp

d = int(sys.argv[1]); a = mp.mpf(sys.argv[2]); N = int(sys.argv[3])
mp.mp.dps = int(sys.argv[4]) if len(sys.argv) > 4 else 120
T0 = time.time()
_cache = {}


def radial(K, n):
    """I(K,n) as the convergent power series in a."""
    key = (K, n)
    if key in _cache:
        return _cache[key]
    total = mp.mpf(0); m = 0; small = 0; peak = mp.mpf(0)
    tol = mp.mpf(10) ** (-mp.mp.dps + 5)
    while True:
        e = mp.mpf(K + 2 * m + 1) / d
        mu = e - 1
        c = mp.mpf(d) ** -1 * (mp.mpf(d) / 2) ** e * mp.mpf(2) ** mu \
            * mp.gamma((n + mu + 1) / 2) * mp.rgamma((n - mu + 1) / 2)
        term = (-a) ** m / mp.factorial(m) * c
        total += term
        peak = max(peak, abs(term))
        small = small + 1 if abs(term) <= tol * max(peak, 1) else 0
        if small > 3 * d and m > 20:
            break
        m += 1
    _cache[key] = (total, m, peak)
    return _cache[key]


def tau(l):
    return (-1) ** (d - 1) if l % d == d - 1 else 1


def rho(n):
    s = (-1) ** n
    for l in range(n):
        s *= tau(l)
    return s


norm = {}
for r in range(min(d, N)):
    k = (N - 1 - r) // d + 1          # block size needed for n < N
    G = mp.matrix(k, k)
    worst = mp.mpf(0)
    for p in range(k):
        for q in range(k):
            nn = abs(p - q)
            I, m, peak = radial(2 * r + d * (p + q) + 1, nn)
            worst = max(worst, peak / max(abs(I), mp.mpf(10) ** -mp.mp.dps))
            G[p, q] = (-1) ** (r + q) * 2 * mp.pi * (1j) ** nn * I
    prev = mp.mpf(1)
    for j in range(k):
        D = mp.det(G[0:j + 1, 0:j + 1])
        norm[r + d * j] = D / prev
        prev = D
    print(f"[{time.time()-T0:7.1f}s] d={d} a={a} class r={r}: block {k}x{k}, "
          f"worst series cancellation 10^{int(mp.log10(worst)) if worst > 0 else 0}",
          flush=True)

ok = True
h = {}
for n in range(N):
    v = norm[n]
    h[n] = rho(n) * v
    im = abs(mp.im(h[n])) / abs(h[n])
    pos = mp.re(h[n]) > 0
    ok &= bool(pos)
    print(f"  n={n:3d} rho={rho(n):+d} h_n={mp.nstr(mp.re(h[n]), 12):>22}  "
          f"{'+' if pos else 'NEGATIVE'}  |Im|/|h|={mp.nstr(im, 3)}", flush=True)

V = {n: mp.re(h[n + 1]) / mp.re(h[n]) for n in range(N - 1)}
getV = lambda n: V[n] if n >= 0 else mp.mpf(0)
worst = mp.mpf(0)
for n in range(N - 1 - (d - 2)):
    s = getV(n)
    for j in range(d - 1):
        prod = mp.mpf(1)
        for k in range(d - 1):
            prod *= getV(n + j - k)
        s += prod / a ** 2
    worst = max(worst, abs(s - (n + 1) / a) / ((n + 1) / a))
print(f"[{time.time()-T0:7.1f}s] d={d} a={a} N={N}: all h_n > 0: {ok}; "
      f"max relative recurrence residual {mp.nstr(worst, 3)}", flush=True)
