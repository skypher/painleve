#!/usr/bin/env python3
"""Local a priori bound test for positive solutions of the general-d recurrence.

Usage: python3 -u local_survival.py [-h|--help] d n [Kmax] [pop] [iters]

Normalized recurrence (eps = 1, L = d - 1): v_j + sum_{m=j-L+1}^{j} T_m = j + 1,
T_m = v_m ... v_{m+L-1}.  Fix an index n and a value v_n = s.  The other
2L - 3 values v_{n-L+1..n+L-2} are free (log-parametrized).  Equation j
determines v_{j+L-1} forward and v_{j-L+1} backward.  For each s, a
cross-entropy search maximizes the number K of steps the orbit stays
positive in BOTH directions (capped at Kmax).  Prints, for s (n+1) on a
log grid, the best K found.  If small s (n+1) caps K at a bounded value,
positivity on a bounded window forces v_n >= c/(n+1).
"""
import sys
if any(x in ("-h", "--help") for x in sys.argv[1:]) or len(sys.argv) < 3:
    print(__doc__); sys.exit(0)
import time
import numpy as np

d = int(sys.argv[1]); n = int(sys.argv[2])
KMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 30
POP = int(sys.argv[4]) if len(sys.argv) > 4 else 4000
ITERS = int(sys.argv[5]) if len(sys.argv) > 5 else 60
L = d - 1
T0 = time.time()
rng = np.random.default_rng(1)
offs = list(range(-L + 1, L - 1))           # seed positions relative to n
free = [o for o in offs if o != 0]


def survival(s, logv):
    """logv: (P, 2L-3) log-values at the free offsets. Returns min(Kf, Kb)."""
    P = logv.shape[0]
    W = KMAX + 2 * L
    v = np.full((P, 2 * W + 1), np.nan)      # index n + o  ->  column W + o
    v[:, W] = s
    for k, o in enumerate(free):
        v[:, W + o] = np.exp(logv[:, k])
    with np.errstate(all='ignore'):
        def T(col_start):                     # product of L entries starting at column
            return np.prod(v[:, col_start:col_start + L], axis=1)
        Kf = np.zeros(P, int); alive = np.ones(P, bool)
        for step in range(KMAX):
            j = W + step                       # equation index n + step
            rest = (n + step + 1) - v[:, j] - sum(T(j + m) for m in range(-L + 1, 0))
            new = rest / np.prod(v[:, j:j + L - 1], axis=1)
            ok = alive & (new > 0) & np.isfinite(new)
            v[:, j + L - 1] = np.where(ok, new, np.nan)
            Kf += ok; alive = ok
        Kb = np.zeros(P, int); alive = np.ones(P, bool)
        for step in range(1, KMAX + 1):
            j = W - step                       # equation index n - step
            Tlow = (n - step + 1) - v[:, j] - sum(T(j + m) for m in range(-L + 2, 1))
            new = Tlow / np.prod(v[:, j - L + 2:j + 1], axis=1)
            ok = alive & (new > 0) & np.isfinite(new) & (n - step - L + 1 >= 0)
            v[:, j - L + 1] = np.where(ok, new, np.nan)
            Kb += ok; alive = ok
    return np.minimum(Kf, Kb), Kf + Kb


lo, hi = np.log(1e-6), np.log(4.0 * (n + 1))
print(f"[{time.time()-T0:6.1f}s] d={d} n={n} Kmax={KMAX} pop={POP} iters={ITERS}; "
      f"true scale v ~ ((n+1)/L)^(1/L) = {((n + 1) / L) ** (1 / L):.3f}", flush=True)
for sn in [1e-3, 1e-2, 0.1, 0.3, 1, 3, 10, 30, 100, (n + 1) * ((n + 1) / L) ** (1 / L)]:
    s = sn / (n + 1)
    mu = rng.uniform(lo, hi, size=len(free)); sig = np.full(len(free), (hi - lo) / 2)
    best = (-1, 0); elite_n = POP // 20
    for it in range(ITERS):
        X = rng.normal(mu, sig, size=(POP, len(free)))
        k, tot = survival(s, X)
        score = k + 1e-3 * tot
        idx = np.argsort(score)[-elite_n:]
        if score[idx[-1]] > best[0] + 1e-9:
            best = (score[idx[-1]], int(k[idx[-1]]))
        mu = X[idx].mean(axis=0); sig = 0.8 * X[idx].std(axis=0) + 0.02
        if best[1] >= KMAX:
            break
    print(f"[{time.time()-T0:6.1f}s] s*(n+1) = {sn:10.4g}  (s = {s:.3e}): best K = {best[1]:3d}"
          f"{'  (cap)' if best[1] >= KMAX else ''}", flush=True)
