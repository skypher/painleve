#!/usr/bin/env python3
"""Numerical uniqueness scan for positive solutions of the quartic recurrence.

Usage: python3 -u scan.py [-h|--help] [a] [N] [grid]

For fixed a, eps = a^-2, iterate
  v_{n+2} = ((n+1) eps / v_n - 1 - v_{n-1} v_{n-2} - v_{n+1} v_{n-1}) / v_{n+1}
from (v0, v1) on a grid around the true Bessel values, in high precision,
and report for each N-level the bounding box of grid points whose orbit stays
positive through index N. Prints one line per level as it finishes.
"""
import sys
if any(x in ("-h", "--help") for x in sys.argv[1:]):
    print(__doc__); sys.exit(0)
import mpmath as mp
import time

mp.mp.dps = 120
a = mp.mpf(sys.argv[1]) if len(sys.argv) > 1 else mp.mpf(1)
NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 60
G = int(sys.argv[3]) if len(sys.argv) > 3 else 41
eps = 1 / a**2
T0 = time.time()


def hB(x):
    X = x**2 / 4
    Jm, Jp = mp.besselj(-0.25, X), mp.besselj(0.25, X)
    return mp.pi**2 * x / 4 * (Jm**2 - mp.sqrt(2) * Jm * Jp + Jp**2)


h0, h1, h2 = hB(a), mp.diff(hB, a), mp.diff(hB, a, 2)
v0t, v1t = -h1 / (a * h0), -h2 / (a * h1)
print(f"[{time.time()-T0:6.1f}s] a={a} eps={mp.nstr(eps,6)} true v0={mp.nstr(v0t,15)} v1={mp.nstr(v1t,15)}", flush=True)


def life(v0, v1, N):
    v = {-2: mp.mpf(0), -1: mp.mpf(0), 0: v0, 1: v1}
    if v0 <= 0 or v1 <= 0:
        return -1
    for m in range(0, N):
        num = (m + 1) * eps / v[m] - 1 - v[m - 1] * v[m - 2] - v[m + 1] * v[m - 1]
        v[m + 2] = num / v[m + 1]
        if v[m + 2] <= 0:
            return m + 1
    return N + 1


for k, width in enumerate([mp.mpf('1e-1'), mp.mpf('1e-3'), mp.mpf('1e-5'), mp.mpf('1e-8')]):
    alive = {}
    for i in range(G):
        for j in range(G):
            d0 = width * (2 * i / (G - 1) - 1)
            d1 = width * (2 * j / (G - 1) - 1)
            alive[(i, j)] = life(v0t + d0, v1t + d1, NMAX)
    for N in [5, 10, 20, 30, 40, 50, NMAX]:
        pts = [(i, j) for (i, j), L in alive.items() if L > N]
        if pts:
            i0 = min(p[0] for p in pts); i1 = max(p[0] for p in pts)
            j0 = min(p[1] for p in pts); j1 = max(p[1] for p in pts)
            scale = 2 * width / (G - 1)
            print(f"[{time.time()-T0:6.1f}s] width={mp.nstr(width,2)} N={N}: {len(pts)} pts alive, "
                  f"box d0∈[{mp.nstr((2*i0/(G-1)-1)*width,3)},{mp.nstr((2*i1/(G-1)-1)*width,3)}] "
                  f"d1∈[{mp.nstr((2*j0/(G-1)-1)*width,3)},{mp.nstr((2*j1/(G-1)-1)*width,3)}]", flush=True)
        else:
            print(f"[{time.time()-T0:6.1f}s] width={mp.nstr(width,2)} N={N}: 0 pts alive", flush=True)
