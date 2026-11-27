#!/usr/bin/env python3
"""
Independent small-N decisions, two methods (neither is the executor's code):

(1) Hand-written exact-cover backtracker over bitmasks (my own):
    state = uncovered bitmask + used-moduli mask; branch on the uncovered
    point with the fewest still-available classes; forward checking only
    (no capacity/density pruning, so this is a genuinely separate search);
    node budget -> INCONCLUSIVE, never a false exclusion.

(2) My own z3 encoding (vfy_sat.decide_case_A style, generalised): sweep of
    all odd N <= 315 -- every such N must come out UNSAT (no covering with
    distinct moduli dividing N), and the backtracker must agree wherever it
    terminates. Sanity: N=12 with the full divisor pool must be COVER
    (classic covering exists), proving the deciders can say yes.
"""
import time
from math import gcd

import z3

from vfy_common import divisors_of, factorize, primes_upto

PRIMES = primes_upto(1000)


# ---------------------------------------------------------------- backtracker
def backtrack_decide(N, pool, node_budget=400_000):
    pool = sorted(pool)
    # classes covering each point: list of (pool_idx, mask)
    coverers = [[] for _ in range(N)]
    class_mask = {}
    for i, d in enumerate(pool):
        for a in range(d):
            mask = 0
            for x in range(a, N, d):
                mask |= 1 << x
            class_mask[(i, a)] = mask
            for x in range(a, N, d):
                coverers[x].append((i, mask))
    full = (1 << N) - 1
    nodes = [0]

    def search(uncovered, used_mask):
        if uncovered == 0:
            return True
        nodes[0] += 1
        if nodes[0] > node_budget:
            raise TimeoutError
        # choose uncovered point with fewest available classes
        best_opts = None
        m = uncovered
        while m:
            lsb = m & -m
            x = lsb.bit_length() - 1
            opts = [(i, mk) for (i, mk) in coverers[x]
                    if not (used_mask >> i) & 1]
            if best_opts is None or len(opts) < len(best_opts):
                best_opts = opts
                if len(opts) <= 1:
                    break
            m ^= lsb
        if not best_opts:
            return False
        for (i, mk) in best_opts:
            if search(uncovered & ~mk, used_mask | (1 << i)):
                return True
        return False

    try:
        return ("COVER" if search(full, 0) else "EXCLUDED"), nodes[0]
    except TimeoutError:
        return "INCONCLUSIVE", nodes[0]


# ---------------------------------------------------------------- z3 sweep
def z3_decide(N, timeout_s=120):
    fac = factorize(N, PRIMES)
    pool = [d for d in divisors_of(fac) if d > 1]
    x = {(m, r): z3.Bool(f"x_{m}_{r}") for m in pool for r in range(m)}
    s = z3.Solver()
    s.set("timeout", int(timeout_s * 1000))
    for m in pool:
        s.add(z3.PbLe([(x[(m, r)], 1) for r in range(m)], 1))
    for z in range(N):
        s.add(z3.Or([x[(m, z % m)] for m in pool]))
    res = s.check()
    if res == z3.sat:
        return "COVER"
    if res == z3.unsat:
        return "EXCLUDED"
    return "INCONCLUSIVE"


def main():
    # sanity: classic covering mod 12 must be found
    pool12 = [d for d in range(2, 13) if 12 % d == 0]
    st, nd = backtrack_decide(12, pool12)
    print(f"sanity N=12 backtracker: {st} (nodes {nd}) -- expect COVER",
          flush=True)

    # backtracker sweep on small odd N
    bt_bad = []
    for N in range(3, 106, 2):
        fac = factorize(N, PRIMES)
        pool = [d for d in divisors_of(fac) if d > 1]
        st, nd = backtrack_decide(N, pool)
        if st != "EXCLUDED":
            bt_bad.append((N, st))
    print(f"backtracker sweep odd N<=105: all EXCLUDED except {bt_bad}",
          flush=True)

    # z3 sweep odd N <= 315
    t0 = time.time()
    z3_bad = []
    for N in range(3, 316, 2):
        st = z3_decide(N)
        if st != "EXCLUDED":
            z3_bad.append((N, st))
    print(f"z3 sweep odd N<=315: all EXCLUDED except {z3_bad} "
          f"({time.time()-t0:.0f}s)", flush=True)


if __name__ == "__main__":
    main()
