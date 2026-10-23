#!/usr/bin/env python3
"""Spot check of Lemma 3 (Hankel sign) for random shapes, m = 2.

Usage: python3 -u lemma3_check.py [-h|--help] [trials] [K]

F(t) = E[exp(-e^t kappa G1 G2)] = E_{G1}[(1 + kappa e^t G1)^{-b2}], G1 ~ Gamma(b1).
With x = kappa G1: F^{(n)}(0) = E[sum_j S(n,j) (-1)^j (b2)_j x^j (1+x)^{-b2-j}].
Checks (-1)^{S_k} det[F^{(p+q)}(0)] > 0 for k <= K.
"""
import sys
if any(x in ("-h", "--help") for x in sys.argv[1:]):
    print(__doc__); sys.exit(0)
import random
import time
import mpmath as mp

TRIALS = int(sys.argv[1]) if len(sys.argv) > 1 else 12
K = int(sys.argv[2]) if len(sys.argv) > 2 else 5
mp.mp.dps = 40
T0 = time.time()
random.seed(7)
bad = 0
for trial in range(TRIALS):
    b1 = mp.mpf(random.uniform(0.05, 3)); b2 = mp.mpf(random.uniform(0.05, 3))
    kappa = mp.mpf(10) ** random.uniform(-2, 2)
    dens = lambda g: g ** (b1 - 1) * mp.exp(-g) / mp.gamma(b1)
    der = []
    for n in range(2 * K - 1):
        def integrand(g, n=n):
            x = kappa * g
            return dens(g) * sum(mp.stirling2(n, j) * (-1) ** j * mp.rf(b2, j)
                                 * x ** j * (1 + x) ** (-b2 - j) for j in range(n + 1))
        der.append(mp.quad(integrand, [0, mp.mpf(1) / 10, 1, 10, mp.inf]))
    signs = []
    for k in range(1, K + 1):
        H = mp.det(mp.matrix([[der[p + q] for q in range(k)] for p in range(k)]))
        val = (-1) ** (k * (k - 1) // 2) * H
        signs.append('+' if val > 0 else 'NEG')
        bad += val <= 0
    print(f"[{time.time()-T0:6.1f}s] b1={mp.nstr(b1, 4)} b2={mp.nstr(b2, 4)} "
          f"kappa={mp.nstr(kappa, 4)}: signs k=1..{K}: {' '.join(signs)}", flush=True)
print(f"[{time.time()-T0:6.1f}s] failures: {bad}", flush=True)
