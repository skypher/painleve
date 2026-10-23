#!/usr/bin/env python3
"""Sanity checks for the reference-solution uniqueness proof.

Usage: python3 -u ref_check.py [-h|--help]

q(t) solves q + L q^L = eps t, q_n = q(n+1), Q_m = q_m ... q_{m+L-1} (0 for m<0).
Prints max_n (n+1)|r_n| for r_n = q_n + sum_{m=n-L+1}^n Q_m - eps(n+1), and,
for the true positive solution (from the moment initial data, a = 1), the
values delta_n = log(v_n/q_n).
"""
import sys
if any(x in ("-h", "--help") for x in sys.argv[1:]):
    print(__doc__); sys.exit(0)
import mpmath as mp
mp.mp.dps = 400


def qfun(t, L, eps):
    return mp.findroot(lambda x: x + L * x ** L - eps * t, (eps * t / L) ** (mp.mpf(1) / L))


def radial(K, d, a):
    total = mp.mpf(0); m = 0; small = 0; peak = mp.mpf(0)
    while True:
        e = mp.mpf(K + 2 * m + 1) / d; mu = e - 1
        c = (mp.mpf(d) / 2) ** e / d * mp.mpf(2) ** mu * mp.gamma((mu + 1) / 2) * mp.rgamma((1 - mu) / 2)
        term = (-a) ** m / mp.factorial(m) * c
        total += term; peak = max(peak, abs(term))
        small = small + 1 if abs(term) <= mp.mpf(10) ** -390 * max(peak, 1) else 0
        if small > 3 * d and m > 20:
            return total
        m += 1


for d in (3, 4, 5, 6):
    L = d - 1; a = mp.mpf(1); eps = a ** (-mp.mpf(d) / (d - 2)); scale = a ** (mp.mpf(2) / (d - 2))
    N = 120
    q = [qfun(n + 1, L, eps) for n in range(N + L)]
    Q = lambda m: mp.fprod(q[m:m + L]) if m >= 0 else mp.mpf(0)
    rmax = max(abs(q[n] + sum(Q(m) for m in range(n - L + 1, n + 1)) - eps * (n + 1)) * (n + 1)
               for n in range(N))
    # true solution from moment data, iterated forward in high precision
    v = [radial(2 * j + 3, d, a) / radial(2 * j + 1, d, a) / scale for j in range(d - 2)]
    T = lambda m: mp.fprod(v[m:m + L]) if m >= 0 else mp.mpf(0)
    for n in range(N):
        rest = (n + 1) * eps - v[n] - sum(T(m) for m in range(n - L + 1, n))
        v.append(rest / mp.fprod(v[n:n + L - 1]))
    dl = [mp.log(v[n] / q[n]) for n in range(N)]
    print(f"d={d}: max (n+1)|r_n| (n<{N}) = {mp.nstr(rmax, 6)};  delta_n at n=0,10,40,80,119: "
          + ", ".join(mp.nstr(dl[n], 4) for n in (0, 10, 40, 80, 119))
          + f";  sum delta^2 = {mp.nstr(mp.fsum(x * x for x in dl), 6)}", flush=True)
