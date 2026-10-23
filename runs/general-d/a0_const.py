#!/usr/bin/env python3
"""Check the limit constant of Corollary cor:endpoint against the series.

Usage: python3 -u a0_const.py [-h|--help] [dmax]

For d = 3..dmax and r = 0..d-1 prints a^{-j_r} M_r(a) at a = 1e-4, 1e-8
(series of a0_check.py) and the closed form
pi r! d^{-(d-2) beta_r} prod_{j in J_r, j != j_r} Gamma(beta_{r,j}-beta_r)/Gamma(beta_{r,j}).
"""
import sys
if any(x in ("-h", "--help") for x in sys.argv[1:]):
    print(__doc__); sys.exit(0)
import time
import mpmath as mp
mp.mp.dps = 40
DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 8
T0 = time.time()


def series(d, r, a, K=60):
    J = [j for j in range(d) if j != d - 1 - r]
    beta = {j: mp.mpf(r + 1 + j) / d for j in J}
    c = mp.mpf(d) ** (d - 2)
    tot = mp.mpf(0)
    for j in J:
        for k in range(K):
            s = beta[j] + k
            term = mp.gamma(s) * c ** (-s) * (-1) ** k / mp.factorial(k) / mp.gamma(beta[j])
            for jj in J:
                if jj != j:
                    term *= mp.gamma(beta[jj] - s) / mp.gamma(beta[jj])
            tot += term * a ** (d * s - r - 1)
    return mp.pi * mp.factorial(r) * tot


worst = 0
for d in range(3, DMAX + 1):
    for r in range(d):
        J = [j for j in range(d) if j != d - 1 - r]
        jr = min(J); br = mp.mpf(r + 1 + jr) / d
        const = mp.pi * mp.factorial(r) * mp.mpf(d) ** (-(d - 2) * br)
        for j in J:
            if j != jr:
                bj = mp.mpf(r + 1 + j) / d
                const *= mp.gamma(bj - br) / mp.gamma(bj)
        vals = [series(d, r, a) / a ** jr for a in (mp.mpf('1e-4'), mp.mpf('1e-8'))]
        rel = abs(vals[1] / const - 1); worst = max(worst, rel)
        print(f"[{time.time()-T0:5.1f}s] d={d} r={r} j_r={jr}: a^-j M(1e-4)={float(vals[0]):.10g} "
              f"a^-j M(1e-8)={float(vals[1]):.10g} const={float(const):.10g} rel={float(rel):.1e}", flush=True)
print(f"worst relative deviation at a=1e-8: {float(worst):.1e}")
