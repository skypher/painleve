#!/usr/bin/env python3
"""Local uniqueness scan for positive solutions of the general-d recurrence.

Usage: python3 -u scan_d.py [-h|--help] d [a] [N] [G] [dps]

Normalized recurrence (v_n = V_n / a^{2/(d-2)}, eps = a^{-d/(d-2)},
L = d - 1): v_n + sum_{m=n-L+1}^{n} T_m = (n+1) eps, T_m = v_m ... v_{m+L-1},
v_k = 0 for k < 0.  The free data are v_0, ..., v_{d-3}; the true values
come from the planar moments V_j = int |z|^{2j+2} rho / int |z|^{2j} rho.
For boxes of shrinking half-width around the true data, iterates a G^(d-2)
grid and prints, for several N, how many grid points stay positive through
index N and the extent of the surviving set along each coordinate (in
units of the half-width).  Extents that shrink in every coordinate as N
grows indicate an isolated positive solution.
"""
import sys
if any(x in ("-h", "--help") for x in sys.argv[1:]) or len(sys.argv) < 2:
    print(__doc__); sys.exit(0)
import itertools
import time
import mpmath as mp

d = int(sys.argv[1]); a = mp.mpf(sys.argv[2]) if len(sys.argv) > 2 else mp.mpf(1)
NMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 60
G = int(sys.argv[4]) if len(sys.argv) > 4 else 15
mp.mp.dps = int(sys.argv[5]) if len(sys.argv) > 5 else 80
L = d - 1
eps = a ** (-mp.mpf(d) / (d - 2))
scale = a ** (mp.mpf(2) / (d - 2))
T0 = time.time()


def radial(K):
    total = mp.mpf(0); m = 0; small = 0; peak = mp.mpf(0)
    tol = mp.mpf(10) ** (-mp.mp.dps + 5)
    while True:
        e = mp.mpf(K + 2 * m + 1) / d
        mu = e - 1
        c = (mp.mpf(d) / 2) ** e / d * mp.mpf(2) ** mu \
            * mp.gamma((mu + 1) / 2) * mp.rgamma((1 - mu) / 2)
        term = (-a) ** m / mp.factorial(m) * c
        total += term; peak = max(peak, abs(term))
        small = small + 1 if abs(term) <= tol * max(peak, 1) else 0
        if small > 3 * d and m > 20:
            return total
        m += 1


true = [radial(2 * j + 3) / radial(2 * j + 1) / scale for j in range(d - 2)]
print(f"[{time.time()-T0:6.1f}s] d={d} a={a} eps={mp.nstr(eps, 8)} true data "
      + ", ".join(mp.nstr(x, 15) for x in true), flush=True)


def life(init, N):
    v = list(init)
    if min(v) <= 0:
        return -1
    get = lambda k: v[k] if k >= 0 else mp.mpf(0)

    def T(m):
        if m < 0:
            return mp.mpf(0)
        p = mp.mpf(1)
        for i in range(L):
            p *= v[m + i]
        return p
    for n in range(N):
        # equation n determines v_{n+L-1}
        rest = (n + 1) * eps - get(n) - sum(T(m) for m in range(n - L + 1, n))
        denom = mp.mpf(1)
        for i in range(L - 1):
            denom *= v[n + i]
        new = rest / denom
        if new <= 0:
            return n + L - 1
        v.append(new)
    return N + L


levels = [n for n in (10, 20, 30, 40, 50, 60, 80, 100) if n <= NMAX]
for width in [mp.mpf('1e-1'), mp.mpf('1e-3'), mp.mpf('1e-6')]:
    grid = [2 * i / mp.mpf(G - 1) - 1 for i in range(G)]
    alive = {}
    for idx in itertools.product(range(G), repeat=d - 2):
        pt = [true[j] * (1 + width * grid[idx[j]]) for j in range(d - 2)]
        alive[idx] = life(pt, NMAX)
    for N in levels:
        pts = [idx for idx, life_n in alive.items() if life_n > N + L - 1]
        if not pts:
            print(f"[{time.time()-T0:6.1f}s] rel. width {mp.nstr(width, 2)} N={N}: none alive",
                  flush=True)
            continue
        ext = []
        for j in range(d - 2):
            lo = min(p[j] for p in pts); hi = max(p[j] for p in pts)
            ext.append(f"[{mp.nstr(grid[lo], 3)},{mp.nstr(grid[hi], 3)}]")
        print(f"[{time.time()-T0:6.1f}s] rel. width {mp.nstr(width, 2)} N={N}: "
              f"{len(pts)}/{len(alive)} alive; extents " + " ".join(ext), flush=True)
