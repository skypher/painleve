#!/usr/bin/env python3
"""Check the product-of-Gammas representation of the class kernels.

Usage: python3 -u gamma_rep.py [-h|--help] [samples]

Claim: with a = 1, W_r(lam) = int |z|^{2r} exp(-|z|^2 + (i lam/d)(z^d + zbar^d)) dA
equals pi r! E[exp(-lam^2 S)], S = d^{d-2} prod_{j in J_r} G_j, with independent
G_j ~ Gamma((r+1+j)/d) and J_r = {0..d-1} minus {d-1-r}.  The left side uses
the exact power series (as in cm.py).  The right side uses one-dimensional
quadrature for d = 3 and Monte Carlo with the given number of samples
(default 2e6) for d = 4..8.
"""
import sys
if any(x in ("-h", "--help") for x in sys.argv[1:]):
    print(__doc__); sys.exit(0)
import time
import mpmath as mp
import numpy as np

SAMPLES = int(float(sys.argv[1])) if len(sys.argv) > 1 else 2_000_000
mp.mp.dps = 60
T0 = time.time()


def W_series(d, r, lam):
    x = mp.mpf(lam) ** 2
    total = mp.mpf(0); m = 0; small = 0; peak = mp.mpf(0)
    while True:
        e = mp.mpf(2 * r + 2 + 2 * m) / d
        mu = e - 1
        c = (mp.mpf(d) / 2) ** e / d * mp.mpf(2) ** mu \
            * mp.gamma((mu + 1) / 2) * mp.rgamma((1 - mu) / 2)
        term = 2 * mp.pi * (-1) ** m / mp.factorial(m) * c * x ** (-mp.mpf(r + 1 + m) / d)
        total += term; peak = max(peak, abs(term))
        small = small + 1 if abs(term) <= mp.mpf(10) ** -50 * peak else 0
        if small > 3 * d and m > 20:
            return total
        m += 1


def shapes(d, r):
    return [mp.mpf(r + 1 + j) / d for j in range(d) if j != d - 1 - r]


def W_gamma_quad(d, r, lam):
    x = mp.mpf(lam) ** 2 * mp.mpf(d) ** (d - 2)
    b = shapes(d, r)
    dens = lambda g, beta: g ** (beta - 1) * mp.exp(-g) / mp.gamma(beta)
    if len(b) == 2:   # E[(1 + x G0)^{-b1}]
        f = lambda g: dens(g, b[0]) * (1 + x * g) ** (-b[1])
        val = mp.quad(f, [0, 1, 10, mp.inf])
    else:             # three shapes
        f = lambda g, h: dens(g, b[0]) * dens(h, b[1]) * (1 + x * g * h) ** (-b[2])
        val = mp.quad(f, [0, 1, 10, mp.inf], [0, 1, 10, mp.inf])
    return mp.pi * mp.factorial(r) * val


def W_gamma_mc(d, r, lam, rng):
    x = float(lam) ** 2 * d ** (d - 2)
    S = np.ones(SAMPLES)
    for beta in shapes(d, r):
        S *= rng.gamma(float(beta), size=SAMPLES)
    vals = np.exp(-x * S)
    return np.pi * float(mp.factorial(r)) * vals.mean(), \
        np.pi * float(mp.factorial(r)) * vals.std() / np.sqrt(SAMPLES)


rng = np.random.default_rng(20261023)
for d in range(3, 9):
    for r in range(d):
        for lam in (0.3, 1.0, 3.0):
            ser = W_series(d, r, lam)
            if d <= 3:
                g = W_gamma_quad(d, r, lam)
                print(f"[{time.time()-T0:6.1f}s] d={d} r={r} lam={lam}: series "
                      f"{mp.nstr(ser, 14)}  gamma {mp.nstr(g, 14)}  "
                      f"rel diff {mp.nstr(abs(ser - g) / abs(g), 3)}", flush=True)
            else:
                g, se = W_gamma_mc(d, r, lam, rng)
                print(f"[{time.time()-T0:6.1f}s] d={d} r={r} lam={lam}: series "
                      f"{mp.nstr(ser, 10)}  MC {g:.6f} +- {se:.1e}  "
                      f"z = {(float(ser) - g) / se:+.2f}", flush=True)
