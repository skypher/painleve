#!/usr/bin/env python3
"""Global scan of initial values (v0, v1) for positive solutions.

Usage: python3 -u globalscan.py [-h|--help] [a] [N] [grid] [levels]

v0 must lie in (0, eps) (equation at n=0); v1 is scanned on (0, V1MAX) in log
scale. Adaptive refinement: at each level, keep cells whose sample survives to
index N_level and subdivide them. Prints surviving-cell counts and bounding
boxes per level, flushed.
"""
import sys
if any(x in ("-h", "--help") for x in sys.argv[1:]):
    print(__doc__); sys.exit(0)
import mpmath as mp
import time

mp.mp.dps = 80
a = mp.mpf(sys.argv[1]) if len(sys.argv) > 1 else mp.mpf(1)
NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 40
G = int(sys.argv[3]) if len(sys.argv) > 3 else 60
LEVELS = int(sys.argv[4]) if len(sys.argv) > 4 else 5
eps = 1 / a**2
T0 = time.time()


def life(v0, v1, N):
    v = {-2: mp.mpf(0), -1: mp.mpf(0), 0: v0, 1: v1}
    for m in range(0, N):
        num = (m + 1) * eps / v[m] - 1 - v[m - 1] * v[m - 2] - v[m + 1] * v[m - 1]
        v[m + 2] = num / v[m + 1]
        if v[m + 2] <= 0:
            return m + 1
    return N + 1


# level 0: uniform in v0 in (0,eps), log-uniform in v1 in (1e-3, 1e3)
cells = []
for i in range(G):
    for j in range(G):
        x0 = eps * (i + 0.5) / G
        y0 = mp.mpf(10) ** (-3 + 6 * (j + 0.5) / G)
        cells.append((x0, y0, eps / G, None))
for lev in range(LEVELS):
    Nlev = min(NMAX, 8 + 8 * lev)
    surv = []
    for (x, y, dx, dy) in cells:
        if life(x, y, Nlev) > Nlev:
            surv.append((x, y, dx, dy))
    if surv:
        xs = [c[0] for c in surv]; ys = [c[1] for c in surv]
        print(f"[{time.time()-T0:6.1f}s] level {lev} N={Nlev}: {len(surv)}/{len(cells)} cells survive; "
              f"v0∈[{mp.nstr(min(xs),8)},{mp.nstr(max(xs),8)}] v1∈[{mp.nstr(min(ys),8)},{mp.nstr(max(ys),8)}]",
              flush=True)
    else:
        print(f"[{time.time()-T0:6.1f}s] level {lev} N={Nlev}: no cell survives", flush=True)
        break
    # refine each surviving cell into 5x5 subcells around its sample, in linear coordinates
    new = []
    for (x, y, dx, dy) in surv:
        ddy = dy if dy is not None else y * (mp.mpf(10) ** (6 / G) - 1)
        for i in range(5):
            for j in range(5):
                new.append((x + dx * (i - 2) / 5, y + ddy * (j - 2) / 5, dx / 5, ddy / 5))
    cells = new[:20000]
