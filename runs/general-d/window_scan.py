#!/usr/bin/env python3
"""Threshold scan: smallest s (n+1) with a positive window solution.

Usage: python3 -u window_scan.py [-h|--help] d n K [starts]

Same window problem as local_window.py.  Bisects (in log s) for the
smallest s at which least_squares finds a residual below 1e-10, over a
range s (n+1) in [1e-8, 1e3], and prints the threshold.
"""
import sys
if any(x in ("-h", "--help") for x in sys.argv[1:]) or len(sys.argv) < 4:
    print(__doc__); sys.exit(0)
import time
import numpy as np
from scipy.optimize import least_squares

d = int(sys.argv[1]); n = int(sys.argv[2]); K = int(sys.argv[3])
STARTS = int(sys.argv[4]) if len(sys.argv) > 4 else 12
L = d - 1
T0 = time.time()
idx = np.arange(n - K - L + 1, n + K + L)
pos = {i: k for k, i in enumerate(idx)}
eqs = np.arange(n - K, n + K + 1)
free = [k for k, i in enumerate(idx) if i != n]
smooth = np.log(((idx + 1.0) / L) ** (1.0 / L))


def residual(x, logs):
    u = np.empty(len(idx)); u[free] = x; u[pos[n]] = logs
    cs = np.concatenate([[0.0], np.cumsum(u)])
    out = np.empty(len(eqs))
    for e, j in enumerate(eqs):
        a = pos[j - L + 1]
        tot = np.exp(u[pos[j]]) + np.exp(cs[a + L:a + 2 * L] - cs[a:a + L]).sum()
        out[e] = (tot - (j + 1)) / (j + 1)
    return out


def feasible(s, warm):
    rng = np.random.default_rng(5)
    starts = ([warm] if warm is not None else []) + [smooth[free]] + \
        [smooth[free] + rng.normal(0, 1.5, len(free)) for _ in range(STARTS)]
    for x0 in starts:
        r = least_squares(residual, x0, args=(np.log(s),), method='trf',
                          xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=3000)
        if np.sqrt(np.mean(r.fun ** 2)) < 1e-10:
            return True, r.x
    return False, None


lo, hi = np.log(1e-8 / (n + 1)), np.log(1e3 / (n + 1))
ok, warm = feasible(np.exp(hi), None)
assert ok, "upper end infeasible"
okl, _ = feasible(np.exp(lo), warm)
if okl:
    print(f"[{time.time()-T0:6.1f}s] d={d} n={n} K={K}: feasible already at s(n+1)=1e-8", flush=True)
    sys.exit(0)
for it in range(14):
    mid = (lo + hi) / 2
    ok, x = feasible(np.exp(mid), warm)
    if ok:
        hi, warm = mid, x
    else:
        lo = mid
print(f"[{time.time()-T0:6.1f}s] d={d} n={n} K={K}: threshold s(n+1) in "
      f"[{np.exp(lo)*(n+1):.3e}, {np.exp(hi)*(n+1):.3e}], i.e. v_n >= {np.exp(lo):.3e} "
      f"= n^{np.log(np.exp(lo))/np.log(n):.3f}", flush=True)
