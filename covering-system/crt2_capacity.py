#!/usr/bin/env python3
"""
Level-2 (intersection-refined) CRT capacity certificate for Erdos #7.

Extends crt_capacity.py (level-1, Mian & Siddique arXiv:2607.25628 Sec. 4.4).
Level-1 bounds the patching capacity of a modulus d not in T by N/d points,
as if a patch class could spend all of its points inside the forced-uncovered
set A_U.  That is wasteful: the exact intersection of a patch class with A_U
is computable, and it is strictly smaller unless the patch modulus is
"aligned" with T.  This module implements the refined bound and validates
its counting formula by brute force before trusting any verdict.

THE REFINED CERTIFICATE (exact statement)
-----------------------------------------
Fix N > 1, pool P(N) = {d : d | N, d > 1}, and T subset of P(N) pairwise
coprime.  For U subset of T and a choice of classes a_t (mod t), t in U, let
A_U subset of [0, N) be the points avoided by every class of U; by CRT
|A_U| = N * prod_{t in U} (1 - 1/t) exactly, whatever the classes are.

For a patch modulus d in P(N) \\ T and a class a (mod d), since d | N,

    max_a |A_U cap (a mod d)|  =  N * (1/d) * prod_{t in U, gcd(d,t)=1} (1 - 1/t).

Reason: the N/d points of the class are distributed over residues mod t
(t | N) as follows.  If gcd(d, t) = 1 they are uniform mod t, so the fraction
(1 - 1/t) of them avoid a_t.  If g = gcd(d, t) > 1 the class pins x mod g to
c = a mod g; choosing c not congruent to a_t (mod g) -- possible since
g >= 2, and simultaneously for all t in U because the g_t are pairwise
coprime divisors of d, so CRT inside d makes the choices independent --
makes EVERY point of the class avoid a_t (fraction 1).  If instead
c = a_t (mod g), the avoided fraction is 1 - g/t < 1, so the adversary
maximising coverage picks the avoiding choice, giving factor 1.

A covering S with U = S cap T needs sum_{d in S\\U} |A_U cap patch_d| >= |A_U|,
and S \\ U subset of P(N) \\ T.  Hence exclusion follows if for EVERY U <= T

    sum_{d in P\\T} (1/d) * prod_{t in U, gcd(d,t)>1} t/(t-1)  <  1.     (dag)

The left side is monotone nondecreasing in U (enlarging U multiplies the
d-term by t/(t-1) >= 1 when gcd(d,t) > 1 and by 1 otherwise), so (dag) only
needs checking at U = T:

    refined_sum(N, T) := sum_{d in P\\T} (1/d) * prod_{t in T, gcd(d,t)>1} t/(t-1)
    refined margin     := 1 - refined_sum(N, T)  >  0   ==>   N excluded.

Level-1 comparison: level-1's condition, divided by prod_T (1 - 1/t), reads
sum_{d not in T} (1/d) * prod_{t in T} t/(t-1) < 1, i.e. it charges EVERY
patch the full factor prod_T t/(t-1); the refined version charges t/(t-1)
only when gcd(d, t) > 1.  So refined_sum <= level-1 normalised sum always:
the refined certificate fires whenever level-1 does, and sometimes when
level-1 does not (10395 is the test case).

All verdict arithmetic is exact (fractions.Fraction).  Brute-force checks
(integer counting on [0, N)) validate the max-intersection formula and the
U = T worst-case claim on small N before any verdict is trusted.

Usage
-----
    python3 crt2_capacity.py --validate        # brute-force formula checks
    python3 crt2_capacity.py --n 10395
    python3 crt2_capacity.py --batch           # all 27 level-1-unresolved
    python3 crt2_capacity.py --selftest        # N=12 must PASS, 945 excluded
"""

import argparse
import itertools
import json
import random
import sys
import time
from fractions import Fraction
from math import gcd

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from search import divisors_gt1, density_sum  # noqa: E402
from crt_capacity import factorize, prime_power_components  # noqa: E402


# ---------------------------------------------------------------- refined sum

def refined_term(d, T):
    """(1/d) * prod_{t in T, gcd(d,t)>1} t/(t-1), exact Fraction."""
    term = Fraction(1, d)
    for t in T:
        if gcd(d, t) > 1:
            term *= Fraction(t, t - 1)
    return term


def refined_sum(n, T, pool=None):
    """Sum of refined terms over the patch pool P(N) \\ T. Exact Fraction."""
    if pool is None:
        pool = divisors_gt1(n, odd_only=False)
    Tset = set(T)
    return sum((refined_term(d, T) for d in pool if d not in Tset), Fraction(0))


def refined_margin(n, T, pool=None):
    """1 - refined_sum.  Certificate (dag) fires iff margin > 0."""
    return Fraction(1) - refined_sum(n, T, pool)


# ---------------------------------------------------------------- T search

def _search_families(n, pool):
    """
    Yield candidate families T: prime family, prime-power choice family,
    and every pairwise-coprime subset of the pool (exhaustive recursion).
    Yields (kind, T).  Exhaustive part may be large; caller dedupes.
    """
    prime_T = tuple(p for (p, _e, _q) in prime_power_components(n))
    yield ("prime", prime_T)
    options = []
    for (p, e, _q) in prime_power_components(n):
        options.append([None] + [p ** f for f in range(1, e + 1)])
    for combo in itertools.product(*options):
        yield ("prime_power_choice", tuple(d for d in combo if d is not None))
    pool = sorted(pool)
    chosen = []

    def rec(i, chosen_prod):
        if i == len(pool):
            yield ("exhaustive", tuple(chosen))
            return
        yield from rec(i + 1, chosen_prod)
        d = pool[i]
        if gcd(d, chosen_prod) == 1:
            chosen.append(d)
            yield from rec(i + 1, chosen_prod * d)
            chosen.pop()

    yield from rec(0, 1)


def best_refined(n, pool=None, node_limit=2_000_000):
    """
    Search T families for the maximum refined margin.
    Returns dict(best_T, best_margin, best_sum, families_checked, completed).
    Duplicate families (same frozenset) are evaluated once.
    """
    if pool is None:
        pool = divisors_gt1(n, odd_only=False)
    seen = set()
    best_T, best_margin = None, None
    checked = 0
    completed = True
    for _kind, T in _search_families(n, pool):
        key = frozenset(T)
        if key in seen:
            continue
        seen.add(key)
        checked += 1
        if checked > node_limit:
            completed = False
            break
        m = refined_margin(n, T, pool)
        if best_margin is None or m > best_margin:
            best_T, best_margin = T, m
    return {"best_T": best_T, "best_margin": best_margin,
            "best_sum": (Fraction(1) - best_margin) if best_margin is not None else None,
            "families_checked": checked, "completed": completed}


def certificate2(n):
    """Full level-2 analysis of one N."""
    t0 = time.perf_counter()
    if n <= 1:
        return {"n": n, "verdict": "NOT_APPLICABLE",
                "elapsed_s": time.perf_counter() - t0}
    pool = divisors_gt1(n, odd_only=False)
    res = best_refined(n, pool)
    verdict = "EXCLUDED_BY_CRT2" if (res["best_margin"] is not None
                                     and res["best_margin"] > 0) else "PASS"
    return {"n": n, "factorization": factorize(n), "pool_size": len(pool),
            "density_sum": density_sum(n, odd_only=False),
            "best_T": res["best_T"], "best_margin": res["best_margin"],
            "best_sum": res["best_sum"],
            "families_checked": res["families_checked"],
            "search_completed": res["completed"],
            "verdict": verdict, "elapsed_s": time.perf_counter() - t0}


# ---------------------------------------------------------------- brute force

def brute_A(n, U, classes):
    """A_U as a boolean list over [0, n): points avoiding every class of U."""
    A = [True] * n
    for t, a in zip(U, classes):
        for x in range(n):
            if x % t == a:
                A[x] = False
    return A


def brute_max_intersection(n, U, classes, d):
    """max over a of |A_U cap (a mod d)|, by direct counting."""
    A = brute_A(n, U, classes)
    best = 0
    for a in range(d):
        cnt = sum(1 for x in range(a, n, d) if A[x])
        best = max(best, cnt)
    return best


def formula_max_intersection(n, U, d):
    """N * (1/d) * prod_{t in U, gcd(d,t)=1} (1 - 1/t), exact Fraction."""
    val = Fraction(n, d)
    for t in U:
        if gcd(d, t) == 1:
            val *= Fraction(t - 1, t)
    return val


def validate_formula(trials=400, seed=20261127):
    """
    Randomised exact check: for small odd N, random pairwise-coprime U,
    random classes, random patch d | N, brute-force max intersection must
    equal the formula.  Also checks the normalised (dag) sum is maximised
    at U = T for random T (monotonicity / worst-case claim).
    """
    rng = random.Random(seed)
    small_N = [105, 315, 945, 1155, 1365, 1995, 3465]
    fails = 0
    for _ in range(trials):
        n = rng.choice(small_N)
        pool = divisors_gt1(n, odd_only=False)
        # random pairwise-coprime U
        shuffled = pool[:]
        rng.shuffle(shuffled)
        U, prod = [], 1
        for d in shuffled:
            if gcd(d, prod) == 1 and rng.random() < 0.6:
                U.append(d)
                prod *= d
        classes = [rng.randrange(t) for t in U]
        d = rng.choice(pool)
        got = brute_max_intersection(n, U, classes, d)
        want = formula_max_intersection(n, U, d)
        if Fraction(got) != want:
            print(f"FORMULA FAIL: n={n} U={U} classes={classes} d={d} "
                  f"brute={got} formula={want}")
            fails += 1
    # monotonicity: normalised sum at U=T dominates all U<T, exact check
    for _ in range(60):
        n = rng.choice(small_N)
        pool = divisors_gt1(n, odd_only=False)
        shuffled = pool[:]
        rng.shuffle(shuffled)
        T, prod = [], 1
        for d in shuffled:
            if gcd(d, prod) == 1 and rng.random() < 0.7:
                T.append(d)
                prod *= d
        Tset = set(T)
        patches = [d for d in pool if d not in Tset]

        def norm_sum(U):
            s = Fraction(0)
            for d in patches:
                term = Fraction(1, d)
                for t in U:
                    if gcd(d, t) > 1:
                        term *= Fraction(t, t - 1)
                s += term
            return s

        full = norm_sum(T)
        for r in range(len(T)):
            for U in itertools.combinations(T, r):
                if norm_sum(list(U)) > full:
                    print(f"MONOTONICITY FAIL: n={n} T={T} U={U}")
                    fails += 1
    print(f"validate: {trials} formula trials + monotonicity checks, "
          f"failures = {fails}")
    return fails == 0


# ---------------------------------------------------------------- reporting

def fmt(fr):
    return f"{fr} (~{float(fr):.6f})" if fr is not None else "None"


def report(res):
    n = res["n"]
    print(f"=== N = {n} (level-2 refined CRT) ===")
    if res["verdict"] == "NOT_APPLICABLE":
        print("verdict: NOT_APPLICABLE")
        return
    fac = " * ".join(f"{p}^{e}" for p, e in sorted(res["factorization"].items()))
    print(f"factorization: {fac}; pool size {res['pool_size']}; "
          f"density sum = {fmt(res['density_sum'])}")
    print(f"best T = {res['best_T']}: refined sum = {fmt(res['best_sum'])}, "
          f"margin = {fmt(res['best_margin'])} "
          f"({res['families_checked']} families, completed={res['search_completed']})")
    print(f"verdict: {res['verdict']}  (elapsed {res['elapsed_s']:.2f} s)")
    print()


UNRESOLVED_27 = [10395, 12285, 17325, 20475, 24255, 26775, 31185, 33075,
                 36855, 45045, 48195, 51975, 58905, 61425, 65835, 69615,
                 72765, 77805, 79695, 80325, 85995, 86625, 89775, 93555,
                 94185, 96525, 99225]


def batch(ns, out_path):
    rows = []
    with open(out_path, "w") as fh:
        for n in ns:
            res = certificate2(n)
            row = {"N": n, "verdict": res["verdict"],
                   "best_T": list(res["best_T"]) if res["best_T"] else None,
                   "best_margin": str(res["best_margin"]),
                   "best_sum": str(res["best_sum"]),
                   "families_checked": res["families_checked"],
                   "search_completed": res["search_completed"],
                   "elapsed_s": round(res["elapsed_s"], 3)}
            fh.write(json.dumps(row) + "\n")
            fh.flush()
            rows.append(row)
            print(f"N={n}: {res['verdict']}  margin={fmt(res['best_margin'])}  "
                  f"T={res['best_T']}  ({res['elapsed_s']:.2f} s)")
    return rows


def selftest():
    ok = True
    r12 = certificate2(12)
    print(f"control N=12 (classic covering exists): verdict = {r12['verdict']} "
          f"(expected PASS), best margin = {fmt(r12['best_margin'])}")
    ok &= r12["verdict"] == "PASS"
    r945 = certificate2(945)
    print(f"target N=945: verdict = {r945['verdict']} (expected EXCLUDED_BY_CRT2), "
          f"margin = {fmt(r945['best_margin'])}")
    ok &= r945["verdict"] == "EXCLUDED_BY_CRT2"
    print(f"SELFTEST {'OK' if ok else 'FAILED'}")
    return 0 if ok else 1


def main(argv=None):
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--n", type=int, default=None)
    ap.add_argument("--batch", action="store_true",
                    help="run the 27 level-1-unresolved candidates")
    ap.add_argument("--out", default="results/crt2_batch_unresolved.jsonl")
    ap.add_argument("--validate", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args(argv)
    if args.validate:
        return 0 if validate_formula() else 1
    if args.selftest:
        return selftest()
    if args.batch:
        batch(UNRESOLVED_27, args.out)
        return 0
    if args.n is not None:
        report(certificate2(args.n))
        return 0
    ap.error("give --n, --batch, --validate or --selftest")


if __name__ == "__main__":
    sys.exit(main())
