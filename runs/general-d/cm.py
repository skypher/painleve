#!/usr/bin/env python3
"""Complete-monotonicity test for the class-r kernels of the general-d form.

Usage: python3 -u cm.py [-h|--help] d [K] [dps]

g_r(x) = W_r(sqrt x), W_r(lam) = int |z|^{2r} exp(-|z|^2 + (i lam/d)(z^d +
zbar^d)) dA (a = 1 without loss of generality: a rescales x).  The d = 4
proof needs g_r = int (1 + x s^2)^{-b} dnu(s) with nu >= 0, which forces
(-1)^k g_r^{(k)}(x) >= 0 for all k.  Uses the series
g_r(x) = 2 pi sum_m (-1)^m/m! c_m x^{-(r+1+m)/d} with exact Mellin
coefficients c_m, and reports, for each r, the first (k, x) with
(-1)^k g_r^{(k)}(x) < 0 for k <= K on a grid of x.
"""
import sys
if any(x in ("-h", "--help") for x in sys.argv[1:]) or len(sys.argv) < 2:
    print(__doc__); sys.exit(0)
import time
import mpmath as mp

d = int(sys.argv[1]); KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 16
mp.mp.dps = int(sys.argv[3]) if len(sys.argv) > 3 else 200
T0 = time.time()
XS = [mp.mpf(10) ** e for e in (-4, -3, -2, -1.5, -1, -0.5, 0, 0.5, 1, 2, 3, 4)]


def coeffs(r, x):
    """Series terms (prefactor, exponent alpha_m) up to convergence at x."""
    out = []; m = 0; small = 0; peak = mp.mpf(0)
    tol = mp.mpf(10) ** (-mp.mp.dps + 10)
    while True:
        e = mp.mpf(2 * r + 2 + 2 * m) / d
        mu = e - 1
        c = mp.mpf(d) ** -1 * (mp.mpf(d) / 2) ** e * mp.mpf(2) ** mu \
            * mp.gamma((mu + 1) / 2) * mp.rgamma((1 - mu) / 2)
        pref = 2 * mp.pi * (-1) ** m / mp.factorial(m) * c
        alpha = mp.mpf(r + 1 + m) / d
        out.append((pref, alpha))
        size = abs(pref) * x ** (-alpha) * mp.rf(alpha, KMAX)
        peak = max(peak, size)
        small = small + 1 if size <= tol * peak else 0
        if small > 3 * d and m > 20:
            return out
        m += 1


for r in range(d):
    first_bad = None
    for x in XS:
        terms = coeffs(r, x)
        for k in range(KMAX + 1):
            val = mp.fsum(p * mp.rf(al, k) * x ** (-al - k) for p, al in terms)
            if val < 0 and first_bad is None:
                first_bad = (k, x, val)
    verdict = "CM on grid" if first_bad is None else \
        f"NOT CM: (-1)^{first_bad[0]} g^({first_bad[0]})({mp.nstr(first_bad[1], 3)}) = {mp.nstr(first_bad[2], 5)}"
    side = "r <= d/2-1" if 2 * r + 2 <= d else "r >= d/2"
    print(f"[{time.time()-T0:6.1f}s] d={d} r={r} ({side}): {verdict}", flush=True)
