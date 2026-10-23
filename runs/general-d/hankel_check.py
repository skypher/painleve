#!/usr/bin/env python3
"""Check Delta_k^(r) = (-1)^{rk} d^{2 S_k} det[F_r^{(p+q)}(0)] and its sign.

Usage: python3 -u hankel_check.py [-h|--help] d a K [dps]

F_r(t) = W_r(a; e^{t/2}) = sum_m c_m e^{-(r+1+m) t/d} (exact series in
x^{-1/d}, x = e^t), so F_r^{(n)}(0) = sum_m c_m (-(r+1+m)/d)^n.  Delta_k^(r)
is the Gram block determinant from the planar moments, computed as in
gram.py.  Prints both sides, their ratio, and sign checks for k <= K.
"""
import sys
if any(x in ("-h", "--help") for x in sys.argv[1:]) or len(sys.argv) < 4:
    print(__doc__); sys.exit(0)
import time
import mpmath as mp

d = int(sys.argv[1]); a = mp.mpf(sys.argv[2]); K = int(sys.argv[3])
mp.mp.dps = int(sys.argv[4]) if len(sys.argv) > 4 else 150
T0 = time.time()


def mellin_coeff(e, n):
    mu = e - 1
    return (mp.mpf(d) / 2) ** e / d * mp.mpf(2) ** mu \
        * mp.gamma((n + mu + 1) / 2) * mp.rgamma((n - mu + 1) / 2)


def radial(Kexp, n):
    """int_0^oo R^K e^{-aR^2} J_n(2R^d/d) dR as a power series in a."""
    total = mp.mpf(0); m = 0; small = 0; peak = mp.mpf(0)
    tol = mp.mpf(10) ** (-mp.mp.dps + 5)
    while True:
        term = (-a) ** m / mp.factorial(m) * mellin_coeff(mp.mpf(Kexp + 2 * m + 1) / d, n)
        total += term; peak = max(peak, abs(term))
        small = small + 1 if abs(term) <= tol * max(peak, 1) else 0
        if small > 3 * d and m > 20:
            return total
        m += 1


def F_derivs(r, nmax):
    """F_r^{(n)}(0) for n <= nmax, with W_r(a; lam) = a^{-r-1} W_r(1; lam a^{-d/2})."""
    # W_r(1; sqrt x) = 2 pi sum_m (-1)^m/m! c_m x^{-(r+1+m)/d};  x = e^t a^{-d}
    out = [mp.mpf(0)] * (nmax + 1)
    m = 0; small = 0; peak = mp.mpf(0)
    tol = mp.mpf(10) ** (-mp.mp.dps + 10)
    while True:
        alpha = mp.mpf(r + 1 + m) / d
        pref = 2 * mp.pi * (-1) ** m / mp.factorial(m) \
            * mellin_coeff(mp.mpf(2 * r + 2 + 2 * m) / d, 0) \
            * a ** (-r - 1) * (a ** (-d)) ** (-alpha)
        size = abs(pref) * max(1, alpha) ** nmax
        for n in range(nmax + 1):
            out[n] += pref * (-alpha) ** n
        peak = max(peak, size)
        small = small + 1 if size <= tol * peak else 0
        if small > 3 * d and m > 20:
            return out
        m += 1


for r in range(d):
    Fd = F_derivs(r, 2 * K - 2)
    G = mp.matrix(K, K)
    for p in range(K):
        for q in range(K):
            nn = abs(p - q)
            G[p, q] = (-1) ** (r + q) * 2 * mp.pi * (1j) ** nn * radial(2 * r + d * (p + q) + 1, nn)
    for k in range(1, K + 1):
        Sk = k * (k - 1) // 2
        Delta = mp.re(mp.det(G[0:k, 0:k]))
        H = mp.det(mp.matrix([[Fd[p + q] for q in range(k)] for p in range(k)]))
        pred = (-1) ** (r * k) * mp.mpf(d) ** (2 * Sk) * H
        print(f"[{time.time()-T0:6.1f}s] d={d} a={a} r={r} k={k}: Delta={mp.nstr(Delta, 12)} "
              f"pred={mp.nstr(pred, 12)} ratio-1={mp.nstr(Delta / pred - 1, 3)} "
              f"sign(H)*(-1)^Sk={'+' if H * (-1) ** Sk > 0 else 'NEG'}", flush=True)
