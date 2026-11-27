#!/usr/bin/env python3
"""
Brute-force validation of the two capacity lemmas on small N.

Level-2 lemma under test: for pairwise coprime forcers T, U subseteq T with
residues a_t, A_U = {x mod N : x != a_t (mod t) for all t in U}, and a patch
class (a mod d):
    max_a |A_U cap (a mod d)| = (N/d) * prod_{t in U, gcd(d,t)=1} (1 - 1/t).
Checked by direct enumeration: for random instances, compute the brute max
over all a and compare with the formula (exact Fraction equality), and check
every fixed a is <= formula.

Level-3 lemma under test: with rho_bar from my own local enumeration,
for every used subset U subseteq F with residues and every patch d notin F:
    |A_U cap (a mod d)| <= |A_U| * prod_p rho_bar_p(v_p(d))   for all a.
Checked by direct enumeration on small N.
"""
import random
from fractions import Fraction
from itertools import combinations
from math import gcd

from vfy_certs import rho_bar_for_prime
from vfy_common import divisors_of, factorize, primes_upto

PRIMES = primes_upto(1000)
rng = random.Random(20261127)


def brute_A(N, used):
    """used: list of (t, a_t). Returns set of x in [0,N) avoiding all."""
    return {x for x in range(N) if all(x % t != a for (t, a) in used)}


def coprime_subsets(pool):
    out = []
    for r in range(len(pool) + 1):
        for comb in combinations(pool, r):
            if all(gcd(comb[i], comb[j]) == 1
                   for i in range(len(comb)) for j in range(i + 1, len(comb))):
                out.append(list(comb))
    return out


def test_level2(trials_per_n=6):
    checks = eq = 0
    fails = []
    for N in [45, 63, 75, 99, 105, 135, 189, 225, 315]:
        fac = factorize(N, PRIMES)
        pool = [d for d in divisors_of(fac) if d > 1]
        families = [T for T in coprime_subsets(pool) if T]
        for _ in range(trials_per_n):
            T = rng.choice(families)
            U = [t for t in T if rng.random() < 0.7]
            used = [(t, rng.randrange(t)) for t in U]
            A = brute_A(N, used)
            d = rng.choice(pool)
            formula = Fraction(N, d)
            for (t, _) in used:
                if gcd(d, t) == 1:
                    formula *= Fraction(t - 1, t)
            brute_max = 0
            for a in range(d):
                v = sum(1 for x in A if x % d == a)
                if v > brute_max:
                    brute_max = v
                checks += 1
                if Fraction(v) > formula:
                    fails.append((N, T, U, d, a, v, str(formula)))
            if Fraction(brute_max) == formula:
                eq += 1
            else:
                fails.append((N, T, U, d, "max", brute_max, str(formula)))
    return checks, eq, fails


def test_level3(trials_per_n=6):
    checks = 0
    fails = []
    for N in [105, 189, 225, 315, 405, 675]:
        fac = factorize(N, PRIMES)
        pool = [d for d in divisors_of(fac) if d > 1]
        prime_powers = sorted({p ** f for p, e in fac.items()
                               for f in range(1, e + 1)})
        rho = {}
        for p, e in fac.items():
            Fp = [f for f in range(1, e + 1) if p ** f in prime_powers]
            rho[p] = rho_bar_for_prime(p, e, Fp)
        F = set(prime_powers)
        for _ in range(trials_per_n):
            used = [(q, rng.randrange(q)) for q in prime_powers
                    if rng.random() < 0.6]
            A = brute_A(N, used)
            if not A:
                continue
            for d in pool:
                if d in F:
                    continue
                bound = Fraction(len(A))
                dfac = factorize(d, PRIMES)
                for p, f in dfac.items():
                    bound *= rho[p][f]
                for a in range(d):
                    v = sum(1 for x in A if x % d == a)
                    checks += 1
                    if Fraction(v) > bound:
                        fails.append((N, used, d, a, v, str(bound)))
    return checks, fails


if __name__ == "__main__":
    c2, eq2, f2 = test_level2()
    print(f"level2 formula: {c2} fixed-a checks, max-equality in {eq2} "
          f"instances, failures: {len(f2)}")
    for f in f2[:5]:
        print("  FAIL", f)
    c3, f3 = test_level3()
    print(f"level3 bound: {c3} fixed-a checks, failures: {len(f3)}")
    for f in f3[:5]:
        print("  FAIL", f)
