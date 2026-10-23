#!/usr/bin/env python3
"""Do the window equations admit positive solutions with a small v_n?

Usage: python3 -u local_window.py [-h|--help] d n K [starts]

Normalized recurrence (eps = 1, L = d - 1): E_j: v_j + sum_{m=j-L+1}^{j} T_m = j + 1.
Unknowns u_i = log v_i for i in [n-K-L+1, n+K+L-1], with u_n = log s fixed;
equations E_j for j in [n-K, n+K] (residuals divided by j + 1).  For each s
on a grid of s (n+1), scipy least_squares minimizes the residual from
several starts (smooth, perturbed, and period-L patterns).  A residual near 0
means a positive local solution with v_n = s exists on the window; a residual
bounded away from 0 means the window equations force v_n > s.
"""
import sys
if any(x in ("-h", "--help") for x in sys.argv[1:]) or len(sys.argv) < 4:
    print(__doc__); sys.exit(0)
import time
import numpy as np
from scipy.optimize import least_squares

d = int(sys.argv[1]); n = int(sys.argv[2]); K = int(sys.argv[3])
STARTS = int(sys.argv[4]) if len(sys.argv) > 4 else 24
L = d - 1
T0 = time.time()
rng = np.random.default_rng(3)
idx = np.arange(n - K - L + 1, n + K + L)        # variable indices
pos = {i: k for k, i in enumerate(idx)}
eqs = np.arange(n - K, n + K + 1)
free = [k for k, i in enumerate(idx) if i != n]


def residual(x, logs):
    u = np.empty(len(idx)); u[free] = x; u[pos[n]] = logs
    v = np.exp(u)
    out = np.empty(len(eqs))
    for e, j in enumerate(eqs):
        tot = v[pos[j]]
        for m in range(j - L + 1, j + 1):
            tot += np.exp(u[pos[m]:pos[m] + L].sum())
        out[e] = (tot - (j + 1)) / (j + 1)
    return out


smooth = np.log(((idx + 1.0) / L) ** (1.0 / L))
print(f"[{time.time()-T0:6.1f}s] d={d} n={n} K={K}: {len(free)} unknowns, {len(eqs)} equations; "
      f"true scale v_n ~ {((n + 1) / L) ** (1 / L):.3f}", flush=True)
for sn in [1e-3, 1e-2, 0.1, 1, 10, 100, 1e3, (n + 1) * ((n + 1) / L) ** (1 / L)]:
    s = sn / (n + 1)
    best = np.inf
    for t in range(STARTS):
        if t == 0:
            x0 = smooth[free]
        elif t < STARTS // 2:
            x0 = smooth[free] + rng.normal(0, 1.5, len(free))
        else:   # period-L pattern: small at residue of n, large elsewhere
            big = np.log(rng.uniform(0.2, 1.0) * (n + 1))
            small = np.log(s) + rng.normal(0, 1)
            pat = np.where((idx - n) % L == 0, small, big + rng.normal(0, 0.5, len(idx)))
            x0 = pat[free]
        r = least_squares(residual, x0, args=(np.log(s),), method='trf',
                          xtol=1e-14, ftol=1e-14, gtol=1e-14, max_nfev=4000)
        best = min(best, np.sqrt(np.mean(r.fun ** 2)))
    print(f"[{time.time()-T0:6.1f}s] s*(n+1) = {sn:10.4g}: min RMS residual = {best:.3e}",
          flush=True)
