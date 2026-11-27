#!/usr/bin/env python3
"""
Independent SAT spot-check (my own encoding, written for this audit).

Decides, for a fixed odd N, whether Z/NZ can be covered by residue classes
with distinct moduli from the pool of divisors of N greater than 1.

Encoding (mine, not copied): boolean x[m][r] = "class r mod m is used".
  - each modulus used at most once: PbLe(sum_r x[m][r]) <= 1
  - every point z covered: Or_m x[m][z mod m]
Symmetry breaking: translation lets us fix the mod-3 class. Two cases:
  (A) modulus 3 used, fixed to class 0 mod 3;
  (B) modulus 3 unused -- killed a priori by the density count
      (sum of 1/d over the remaining pool < 1), which this script verifies
      in exact rationals before declaring case B impossible.
So only case (A) is handed to z3.

Usage: python3 vfy_sat.py 945 1575   (writes sat_spotcheck.json)
"""
import json
import sys
import time
from fractions import Fraction

import z3

from vfy_common import factorize, pool_of, primes_upto

PRIMES = primes_upto(100000)


def density_without(n, banned):
    fac = factorize(n, PRIMES)
    pool = pool_of(fac)
    return sum((Fraction(1, d) for d in pool if d not in banned), Fraction(0))


def decide_case_A(n, timeout_s):
    fac = factorize(n, PRIMES)
    pool = pool_of(fac)
    x = {}
    for m in pool:
        for r in range(m):
            x[(m, r)] = z3.Bool(f"x_{m}_{r}")
    s = z3.Solver()
    s.set("timeout", int(timeout_s * 1000))
    for m in pool:
        s.add(z3.PbLe([(x[(m, r)], 1) for r in range(m)], 1))
    for z in range(n):
        s.add(z3.Or([x[(m, z % m)] for m in pool]))
    # case A: modulus 3 used as class 0
    s.add(x[(3, 0)])
    t0 = time.time()
    res = s.check()
    dt = time.time() - t0
    out = {"N": n, "case": "A (3 used as 0 mod 3)", "result": str(res),
           "seconds": round(dt, 2), "variables": len(x)}
    if res == z3.sat:
        mdl = s.model()
        classes = [(r, m) for (m, r), v in x.items()
                   if z3.is_true(mdl.eval(v, model_completion=True))]
        # self-verify the found cover by direct enumeration
        covered = bytearray(n)
        for (a, m) in classes:
            for t in range(a, n, m):
                covered[t] = 1
        out["classes"] = sorted(classes)
        out["self_verified_cover"] = bool(all(covered))
    return out


def main():
    targets = [int(a) for a in sys.argv[1:]] or [945, 1575]
    results = []
    for n in targets:
        dens_b = density_without(n, banned={3})
        entry = {"N": n,
                 "case_B_density_without_3": str(dens_b),
                 "case_B_impossible_by_density": bool(dens_b < 1)}
        if dens_b < 1:
            entry["case_A"] = decide_case_A(n, timeout_s=1200)
        results.append(entry)
        print(json.dumps(entry), flush=True)
    with open("sat_spotcheck.json", "w") as f:
        json.dump(results, f, indent=1)


if __name__ == "__main__":
    main()
