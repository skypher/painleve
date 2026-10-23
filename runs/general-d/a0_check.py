#!/usr/bin/env python3
"""Behaviour of the diagonal Gram entries as a -> 0+.

Usage: python3 -u a0_check.py [-h|--help] [dmax]

For d = 2..dmax and r = 0..d-1 compares
  M_r(a) = int_C |z|^{2r} rho_a dA = pi int_0^inf u^r e^{-au} J_0((2/d) u^{d/2}) du
(direct oscillatory quadrature, a = 1 and a = 0.5) with the small-a series
  M_r(a) = sum_{j in J_r, k >= 0} c_{j,k} a^{j+dk}
obtained from the residues of the Mellin transform in Proposition 4.1
(convergent for d >= 3; for d = 2 compared with pi a^r-closed forms).
Prints M_r(a) for a in {1e-1, 1e-2, 1e-3} and the limit M_r(0) = c_{0,0}
(zero when 0 is not in J_r, i.e. r = d-1).
"""
import sys
if any(x in ("-h", "--help") for x in sys.argv[1:]):
    print(__doc__); sys.exit(0)
import time
import mpmath as mp

mp.mp.dps = 40
DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
T0 = time.time()


def series(d, r, a, K=200):
    J = [j for j in range(d) if j != d - 1 - r]
    beta = {j: mp.mpf(r + 1 + j) / d for j in J}
    c = mp.mpf(d) ** (d - 2)
    tot = mp.mpf(0)
    for j in J:
        b = beta[j]
        for k in range(K):
            s = b + k
            term = mp.gamma(s) * c ** (-s) * (-1) ** k / mp.factorial(k) / mp.gamma(b)
            for jj in J:
                if jj != j:
                    term *= mp.gamma(beta[jj] - s) / mp.gamma(beta[jj])
            # g(x) term x^{-s} with x = a^{-d}, times a^{-r-1}
            tot += term * a ** (d * s - r - 1)
    return mp.pi * mp.factorial(r) * tot


def direct(d, r, a):
    f = lambda u: u ** r * mp.exp(-a * u) * mp.besselj(0, mp.mpf(2) / d * u ** (mp.mpf(d) / 2))
    # split at points where the Bessel argument passes multiples of pi
    pts = [mp.mpf(0)] + [((mp.pi * n * d / 2)) ** (mp.mpf(2) / d) for n in range(1, 4000)]
    tot = mp.mpf(0)
    for lo, hi in zip(pts[:-1], pts[1:]):
        tot += mp.quad(f, [lo, hi])
        if mp.exp(-a * hi) * hi ** r < mp.mpf(10) ** (-30):
            break
    return mp.pi * tot


for d in range(2, DMAX + 1):
    for r in range(d):
        line = f"[{time.time()-T0:6.1f}s] d={d} r={r}:"
        if d == 2:
            closed = {0: lambda a: mp.pi / mp.sqrt(a * a + 1),
                      1: lambda a: mp.pi * a / (a * a + 1) ** mp.mpf(1.5)}[r]
            for a in (mp.mpf(1), mp.mpf('0.5')):
                line += f" a={float(a)}: direct/closed-1 = {float(direct(d, r, a)/closed(a)-1):.1e};"
            for a in (mp.mpf('0.1'), mp.mpf('0.01'), mp.mpf('0.001'), mp.mpf(0)):
                line += f" M({float(a)})={float(closed(a)):.6g}"
        else:
            for a in (mp.mpf(1), mp.mpf('0.5')):
                line += f" a={float(a)}: direct/series-1 = {float(direct(d, r, a)/series(d, r, a)-1):.1e};"
            for a in (mp.mpf('0.1'), mp.mpf('0.01'), mp.mpf('0.001')):
                line += f" M({float(a)})={float(series(d, r, a)):.6g}"
            line += f" M(0)={float(series(d, r, mp.mpf(0)) if d - 1 - r != 0 else 0):.6g}"
        print(line, flush=True)
