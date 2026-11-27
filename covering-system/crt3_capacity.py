#!/usr/bin/env python3
"""
Level-3 (per-prime exact, prime-power forcer family) capacity certificate.

Generalises crt2_capacity.py.  Level-2 forces with a pairwise-coprime family
T and bounds a patch class's intersection with the forced-uncovered set A_U
by a gcd factor.  Level-3 allows the forcer family F to contain several
prime powers of the SAME prime (e.g. 3, 9, 27), where level-2's product
formula no longer applies.  Everything is computed prime by prime, exactly.

Setup: N fixed, pool P(N) = {d : d | N, d > 1}, F subset of P(N) the forcer
family (default: all prime powers p^f | N).  For a hypothetical covering S
let U = S cap F with chosen classes; A_U = points of [0, N) avoiding every
class of U.  CRT splits [0, N) as a product over p | N of Z/p^{e_p}Z, and
A_U = prod_p A^{(p)}, where A^{(p)} depends only on the LOCAL configuration
at p: which prime powers p^f in F are used at p and with which classes.

For a patch modulus d (in P(N) \\ F) and f = v_p(d):
    max_a |A_U cap (a mod d)| = prod_p g_p^{gamma_p}(f),
    g_p^{gamma}(f) := max over classes c mod p^f of |A^{(p)}_gamma cap c|,
because patch classes are chosen independently at each prime (CRT).
Define the per-prime worst-case ratio
    rho_bar_p(f) := max_gamma  g_p^{gamma}(f) / |A^{(p)}_gamma|
over all local configurations gamma at p (subsets of F's p-parts, all class
choices).  Local configurations at distinct primes are independent when F
consists of prime powers, and in any case each factor of the true term is
<= rho_bar_p(f), so for EVERY covering and every U:

    |A_U cap patch_d| <= |A_U| * prod_p rho_bar_p(v_p(d)) =: |A_U| * term_bar(d).

Hence the sufficient exclusion condition
    sum_{d in P(N) \\ F} term_bar(d)  <  1        (dag3)
(margin3 := 1 - that sum > 0).  With F = set of primes of N, (dag3) reduces
exactly to the level-2 condition at T = primes (checked in --validate).

Safety: with F = prime powers, |A^{(p)}| > 0 for every local configuration,
because the classes available at p have total density
sum_{f>=1} p^{-f} = 1/(p-1) <= 1/2 < 1; the code asserts this.

All arithmetic exact (fractions.Fraction); local sets are computed by
brute force over Z/p^eZ (p^e <= 3^12 guard not needed here: p^e <= 27 for
the target N; a size guard raises for p^e > 200000).

Usage
-----
    python3 crt3_capacity.py --validate
    python3 crt3_capacity.py --n 675675
    python3 crt3_capacity.py --selftest     # N=12 must PASS, 945 excluded
"""

import argparse
import itertools
import random
import sys
import time
from fractions import Fraction
from math import gcd

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from search import divisors_gt1, density_sum  # noqa: E402
from crt_capacity import factorize, prime_power_components  # noqa: E402
from crt2_capacity import refined_sum  # noqa: E402


# ---------------------------------------------------------------- local data

def _local_configs(p, e, parts):
    """
    All local configurations at prime p (exponent e in N) from forcer parts
    `parts` = list of f values (1<=f<=e) whose prime power p^f is in F.
    A configuration chooses a subset of parts and a class for each.
    Returns a set of signatures (A_count, g_tuple) with g_tuple[f] =
    max over classes mod p^f of |A cap class|, f = 0..e (g[0] = A_count).
    Brute force over Z/p^eZ.
    """
    q = p ** e
    if q > 200_000:
        raise ValueError(f"prime power {p}^{e} too large for brute force")
    sigs = set()
    options = []
    for f in parts:
        mod = p ** f
        options.append([None] + list(range(mod)))
    for combo in itertools.product(*options):
        forbidden = [False] * q
        for f, a in zip(parts, combo):
            if a is None:
                continue
            mod = p ** f
            for x in range(a, q, mod):
                forbidden[x] = True
        A = [x for x in range(q) if not forbidden[x]]
        if not A:
            # Cannot happen for prime-power forcers (density < 1); if it
            # ever does, the certificate framework needs that U handled
            # separately -- fail loudly rather than silently.
            raise AssertionError(f"empty A^(p) at p={p}, combo={combo}")
        g = [0] * (e + 1)
        g[0] = len(A)
        inset = [False] * q
        for x in A:
            inset[x] = True
        for f in range(1, e + 1):
            mod = p ** f
            bins = [0] * mod
            for x in A:
                bins[x % mod] += 1
            g[f] = max(bins)
        sigs.add((len(A), tuple(g)))
    return sigs


def rho_bar(p, e, parts):
    """
    rho_bar[f] = max over local configurations of g[f] / A_count, f = 0..e.
    Exact Fractions.  rho_bar[0] = 1 always.
    """
    sigs = _local_configs(p, e, parts)
    out = []
    for f in range(e + 1):
        out.append(max(Fraction(g[f], cnt) for (cnt, g) in sigs))
    return out


def prime_power_family(n):
    """All prime powers p^f (1<=f<=e) dividing n."""
    return sorted(p ** f for (p, e, _q) in prime_power_components(n)
                  for f in range(1, e + 1))


def certificate3(n, F=None):
    """Level-3 analysis of one N.  F defaults to all prime powers | N."""
    t0 = time.perf_counter()
    if n <= 1:
        return {"n": n, "verdict": "NOT_APPLICABLE",
                "elapsed_s": time.perf_counter() - t0}
    if F is None:
        F = prime_power_family(n)
    Fset = set(F)
    pool = divisors_gt1(n, odd_only=False)
    comps = prime_power_components(n)
    rb = {}
    for (p, e, _q) in comps:
        parts = [f for f in range(1, e + 1) if p ** f in Fset]
        rb[p] = rho_bar(p, e, parts)
    total = Fraction(0)
    terms = {}
    for d in pool:
        if d in Fset:
            continue
        term = Fraction(1)
        m = d
        for (p, e, _q) in comps:
            f = 0
            while m % p == 0:
                m //= p
                f += 1
            term *= rb[p][f]
        terms[d] = term
        total += term
    margin = Fraction(1) - total
    return {"n": n, "factorization": factorize(n), "F": F,
            "rho_bar": {p: rb[p] for p in rb},
            "sum": total, "margin": margin, "terms": terms,
            "verdict": "EXCLUDED_BY_CRT3" if margin > 0 else "PASS",
            "elapsed_s": time.perf_counter() - t0}


# ---------------------------------------------------------------- validation

def validate(seed=777):
    """
    (a) F = primes must reproduce level-2's refined sum at T = primes.
    (b) Brute-force: for small N, random U subset of F (prime powers) and
        random classes, sum_d max_a |A_U cap patch_d| must be
        <= |A_U| * (level-3 sum).  Direct counting over [0, N).
    """
    ok = True
    # (a)
    for n in (945, 10395, 12285, 675675):
        primes = [p for (p, _e, _q) in prime_power_components(n)]
        r3 = certificate3(n, F=primes)
        r2 = refined_sum(n, tuple(primes))
        match = r3["sum"] == r2
        print(f"consistency n={n}: level3(F=primes) sum={r3['sum']} "
              f"vs level2 refined sum={r2}  equal={match}")
        ok &= match
    # (b)
    rng = random.Random(seed)
    for n in (105, 315, 1155, 3465):
        F = prime_power_family(n)
        Fset = set(F)
        pool = divisors_gt1(n, odd_only=False)
        patches = [d for d in pool if d not in Fset]
        r3 = certificate3(n)
        bound = r3["sum"]
        for _ in range(12):
            U = [m for m in F if rng.random() < 0.5]
            classes = [rng.randrange(m) for m in U]
            A = [True] * n
            for m, a in zip(U, classes):
                for x in range(a, n, m):
                    A[x] = False
            cardA = sum(A)
            lhs = 0
            for d in patches:
                bins = [0] * d
                for x in range(n):
                    if A[x]:
                        bins[x % d] += 1
                lhs += max(bins)
            rhs = Fraction(cardA) * bound
            if Fraction(lhs) > rhs:
                print(f"BOUND FAIL n={n} U={U} classes={classes}: "
                      f"brute {lhs} > bound {rhs}")
                ok = False
        print(f"brute bound check n={n}: level3 sum={bound} "
              f"(~{float(bound):.4f}), 12 random (U, classes) checked")
    print(f"VALIDATE {'OK' if ok else 'FAILED'}")
    return ok


def selftest():
    ok = True
    r12 = certificate3(12)
    print(f"control N=12 (classic covering exists): verdict = {r12['verdict']} "
          f"(expected PASS), margin = {r12['margin']} (~{float(r12['margin']):.6f})")
    ok &= r12["verdict"] == "PASS"
    r945 = certificate3(945)
    print(f"target N=945: verdict = {r945['verdict']} (expected EXCLUDED_BY_CRT3), "
          f"margin = {r945['margin']} (~{float(r945['margin']):.6f})")
    ok &= r945["verdict"] == "EXCLUDED_BY_CRT3"
    print(f"SELFTEST {'OK' if ok else 'FAILED'}")
    return 0 if ok else 1


def report(res):
    n = res["n"]
    print(f"=== N = {n} (level-3 per-prime CRT) ===")
    if res["verdict"] == "NOT_APPLICABLE":
        print("verdict: NOT_APPLICABLE")
        return
    fac = " * ".join(f"{p}^{e}" for p, e in sorted(res["factorization"].items()))
    print(f"factorization: {fac}")
    print(f"forcer family F = {res['F']}")
    for p, rbv in sorted(res["rho_bar"].items()):
        print(f"  rho_bar[{p}] = {[str(x) for x in rbv]} "
              f"(~{[round(float(x), 6) for x in rbv]})")
    print(f"level-3 sum = {res['sum']} (~{float(res['sum']):.6f}), "
          f"margin = {res['margin']} (~{float(res['margin']):.6f})")
    print(f"verdict: {res['verdict']}  (elapsed {res['elapsed_s']:.2f} s)")
    print()


def main(argv=None):
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--n", type=int, default=None)
    ap.add_argument("--validate", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args(argv)
    if args.validate:
        return 0 if validate() else 1
    if args.selftest:
        return selftest()
    if args.n is not None:
        report(certificate3(args.n))
        return 0
    ap.error("give --n, --validate or --selftest")


if __name__ == "__main__":
    sys.exit(main())
