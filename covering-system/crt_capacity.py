#!/usr/bin/env python3
"""
CRT capacity certificate for the Erdos-Selfridge odd covering problem (Erdos #7).

Implements the certificate of Mian & Siddique, arXiv:2607.25628, Section 4.4
(Theorem 4.4, "capacity_exclusion"), plus a per-prime-power component screen
(the weaker decomposition suggested in the project plan; see crt_notes.md for
why the screen alone cannot exclude and the joint CRT inequality can).

THE CERTIFICATE (exact statement)
---------------------------------
Fix N > 1. Let P(N) = {d : d | N, d > 1} be the modulus pool. Let T subset of
P(N) be pairwise coprime. If

    sum_{d in P(N), d not in T}  1/d   <   prod_{d in T} (1 - 1/d)      (*)

then NO family of congruence classes with distinct moduli > 1, all dividing N,
covers Z/NZ (hence none covers Z with lcm dividing N).

Why (*) is sufficient (proof sketch; full version in crt_notes.md):
  Let S be a hypothetical covering, U = S cap T the classes whose moduli lie
  in T. By CRT, for each d in U one may choose a residue mod d different from
  the class residue; the prod_{d in U} (d-1) simultaneous choices give points
  of [0, N) avoided by every class of U, each recurring N / prod(U) times, so
  U leaves at least N * prod_{d in U} (1 - 1/d) >= N * prod_{d in T} (1 - 1/d)
  points uncovered (fewer factors <= 1 only enlarge the product: this is the
  paper's monotone-relaxation step). The classes that could patch those points
  are S \\ U, and S \\ U subset of P(N) \\ T (anything of S inside T is in U),
  each patching at most N/d points, so total patch capacity is at most
  sum_{d in P(N) \\ T} N/d. If (*) holds, capacity < forced-uncovered: no cover.

Verdicts
--------
  EXCLUDED_BY_CRT : some pairwise-coprime T satisfies (*)  -> N is excluded.
  PASS            : no T in the searched families satisfies (*). This is NOT
                    a claim that a covering exists; the certificate simply
                    does not fire (cf. the paper's straggler 10395).
  NOT_APPLICABLE  : N <= 1 (no modulus pool).

Search space for T
------------------
  (i)  "prime-power choice": for each prime p || N choose at most one prime
       power p^f (1 <= f <= v_p(N)) -- includes the paper's prime family
       {p} and the prime-power towers p^{v_p(N)}.
  (ii) "exhaustive": every pairwise-coprime subset of the whole pool P(N)
       (feasible for the pool sizes here, |P| <= 23; node count reported).
  The verdict uses (ii) when it completes; (i) is reported alongside.

Per-prime-power component screen (necessary-condition data, NOT a certificate)
--------------------------------------------------------------------------------
  For q = p^e || N, project a covering of Z/NZ onto Z/qZ (CRT component).
  A class mod m projects into a single class mod gcd(m, q) =: m_p (its p-part),
  covering the fraction 1/m_p of Z/qZ if m_p > 1, and the whole component if
  m_p = 1. A union bound over the pool gives
      cap_q = min(1, sum_{m in P(N)} frac_q(m)),  frac_q(m) = 1/m_p or 1.
  cap_q < 1 would exclude N, but whenever the pool contains a modulus coprime
  to p (e.g. another prime divisor of N), frac_q = 1 and cap_q = 1: the screen
  is then vacuous. It is reported for honesty/comparison only; the exclusion
  verdict never rests on it.

All arithmetic is exact (fractions.Fraction). No floats enter any verdict;
floats are printed only as decimal approximations for readability.

Usage
-----
    python3 crt_capacity.py --n 945
    python3 crt_capacity.py --all          # 945, 1575, 2205
    python3 crt_capacity.py --selftest     # controls: N=12 must PASS (classic
                                           # covering exists), N=10395 must PASS
                                           # (paper's straggler), 945 EXCLUDED
"""

import argparse
import itertools
import sys
import time
from fractions import Fraction
from math import gcd

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from search import divisors_gt1, density_sum, sieve_pass  # noqa: E402


# ---------------------------------------------------------------- factorisation

def factorize(n):
    """Return {p: e} for n >= 2."""
    out = {}
    d = 2
    m = n
    while d * d <= m:
        while m % d == 0:
            out[d] = out.get(d, 0) + 1
            m //= d
        d += 1 if d == 2 else 2
    if m > 1:
        out[m] = out.get(m, 0) + 1
    return out


def prime_power_components(n):
    """[(p, e, p**e)] with p**e || n, sorted by p."""
    return [(p, e, p ** e) for p, e in sorted(factorize(n).items())]


# ---------------------------------------------------------------- component screen

def component_screen(n):
    """
    Per-prime-power CRT component data (see module docstring).
    Returns list of dicts with exact Fractions.
    """
    pool = divisors_gt1(n, odd_only=False)
    rows = []
    for (p, e, q) in prime_power_components(n):
        per_modulus = []
        total = Fraction(0)
        for m in pool:
            m_p = gcd(m, q)  # p-part of m, since q = p^e || n and m | n
            frac = Fraction(1) if m_p == 1 else Fraction(1, m_p)
            per_modulus.append((m, m_p, frac))
            total += frac
        rows.append({
            "p": p, "e": e, "q": q,
            "pool_projection": per_modulus,
            "raw_capacity_sum": total,
            "capacity_capped": min(Fraction(1), total),
            "vacuous": any(mp == 1 for (_, mp, _) in per_modulus),
        })
    return rows


# ---------------------------------------------------------------- CRT certificate

def crt_margin(n, T, pool=None):
    """
    margin(T) = prod_{d in T} (1 - 1/d) - sum_{d in pool, d not in T} 1/d.
    Certificate (*) fires iff margin > 0. Exact Fraction.
    """
    if pool is None:
        pool = divisors_gt1(n, odd_only=False)
    Tset = set(T)
    rhs = Fraction(1)
    for d in T:
        rhs *= Fraction(d - 1, d)
    lhs = sum((Fraction(1, d) for d in pool if d not in Tset), Fraction(0))
    return rhs - lhs, lhs, rhs


def pairwise_coprime(T):
    prod = 1
    for d in T:
        if gcd(d, prod) != 1:
            return False
        prod *= d
    return True


def search_prime_power_choice(n, pool):
    """
    Families T choosing at most one prime power p^f (1<=f<=e) per prime p||n.
    Returns (best_T, best_margin, n_families_checked).
    """
    options = []
    for (p, e, _q) in prime_power_components(n):
        options.append([None] + [p ** f for f in range(1, e + 1)])
    best_T, best_margin, checked = None, None, 0
    for combo in itertools.product(*options):
        T = tuple(d for d in combo if d is not None)
        checked += 1
        margin, _, _ = crt_margin(n, T, pool)
        if best_margin is None or margin > best_margin:
            best_T, best_margin = T, margin
    return best_T, best_margin, checked


def search_exhaustive(n, pool, node_limit=5_000_000):
    """
    All pairwise-coprime subsets of the pool, by recursion.
    Returns (best_T, best_margin, nodes, completed_bool).
    """
    pool = sorted(pool)
    best = {"T": None, "margin": None}
    nodes = [0]
    aborted = [False]

    def rec(i, chosen, chosen_prod):
        if aborted[0]:
            return
        nodes[0] += 1
        if nodes[0] > node_limit:
            aborted[0] = True
            return
        if i == len(pool):
            margin, _, _ = crt_margin(n, chosen, pool)
            if best["margin"] is None or margin > best["margin"]:
                best["T"], best["margin"] = tuple(chosen), margin
            return
        # exclude pool[i]
        rec(i + 1, chosen, chosen_prod)
        # include pool[i] if coprime to everything chosen
        d = pool[i]
        if gcd(d, chosen_prod) == 1:
            rec(i + 1, chosen + [d], chosen_prod * d)

    rec(0, [], 1)
    return best["T"], best["margin"], nodes[0], not aborted[0]


def certificate(n):
    """Full analysis of one N. Returns a dict of exact results."""
    t0 = time.perf_counter()
    if n <= 1:
        return {"n": n, "verdict": "NOT_APPLICABLE",
                "elapsed_s": time.perf_counter() - t0}
    pool = divisors_gt1(n, odd_only=False)
    dens = density_sum(n, odd_only=False)
    prime_T = tuple(p for (p, _e, _q) in prime_power_components(n))
    prime_margin, prime_lhs, prime_rhs = crt_margin(n, prime_T, pool)
    pp_T, pp_margin, pp_checked = search_prime_power_choice(n, pool)
    ex_T, ex_margin, ex_nodes, ex_done = search_exhaustive(n, pool)
    # verdict rests on the strongest completed search
    candidates = [(prime_T, prime_margin), (pp_T, pp_margin)]
    if ex_done:
        candidates.append((ex_T, ex_margin))
    best_T, best_margin = max(candidates, key=lambda tm: tm[1])
    verdict = "EXCLUDED_BY_CRT" if best_margin > 0 else "PASS"
    return {
        "n": n,
        "factorization": factorize(n),
        "components": prime_power_components(n),
        "pool": pool,
        "density_sum": dens,
        "sieve_pass": dens >= 1,
        "component_screen": component_screen(n),
        "prime_family": {"T": prime_T, "margin": prime_margin,
                         "lhs": prime_lhs, "rhs": prime_rhs},
        "prime_power_choice": {"T": pp_T, "margin": pp_margin,
                               "families_checked": pp_checked},
        "exhaustive": {"T": ex_T, "margin": ex_margin,
                       "nodes": ex_nodes, "completed": ex_done},
        "best_T": best_T,
        "best_margin": best_margin,
        "verdict": verdict,
        "elapsed_s": time.perf_counter() - t0,
    }


# ---------------------------------------------------------------- reporting

def fmt(fr):
    return f"{fr} (~{float(fr):.6f})"


def report(res):
    n = res["n"]
    print(f"=== N = {n} ===")
    if res["verdict"] == "NOT_APPLICABLE":
        print("verdict: NOT_APPLICABLE (N <= 1, no modulus pool)")
        return
    fac = " * ".join(f"{p}^{e}" for p, e in sorted(res["factorization"].items()))
    print(f"factorization: {fac}")
    print(f"pool P(N) ({len(res['pool'])} moduli): {res['pool']}")
    print(f"density sum sum_{{d|N,d>1}} 1/d = {fmt(res['density_sum'])} "
          f"(density sieve: {'PASS' if res['sieve_pass'] else 'FAIL'})")
    print("per-prime-power component screen (necessary-condition data only):")
    for row in res["component_screen"]:
        print(f"  q = {row['p']}^{row['e']} = {row['q']}: "
              f"raw union-bound capacity sum = {fmt(row['raw_capacity_sum'])}, "
              f"capped = {row['capacity_capped']}, "
              f"vacuous (pool has a modulus coprime to {row['p']}): {row['vacuous']}")
    pf = res["prime_family"]
    print(f"paper prime family T = {pf['T']}: "
          f"sum_{{d not in T}} 1/d = {fmt(pf['lhs'])}, "
          f"prod_{{d in T}} (1-1/d) = {fmt(pf['rhs'])}, "
          f"margin = {fmt(pf['margin'])}")
    pp = res["prime_power_choice"]
    print(f"best prime-power-choice family T = {pp['T']}: margin = {fmt(pp['margin'])} "
          f"({pp['families_checked']} families checked)")
    ex = res["exhaustive"]
    print(f"best exhaustive pairwise-coprime family T = {ex['T']}: "
          f"margin = {fmt(ex['margin'])} "
          f"(search completed: {ex['completed']}, nodes = {ex['nodes']})")
    print(f"BEST margin = {fmt(res['best_margin'])} with T = {res['best_T']}")
    print(f"verdict: {res['verdict']}")
    print(f"elapsed: {res['elapsed_s']:.3f} s")
    print()


def selftest():
    ok = True
    # Soundness control: N=12 hosts the classic covering, certificate must NOT fire.
    r12 = certificate(12)
    print(f"control N=12 (classic covering exists): verdict = {r12['verdict']} "
          f"(expected PASS), best margin = {fmt(r12['best_margin'])}")
    ok &= r12["verdict"] == "PASS"
    # Limit control: 10395 is the paper's first straggler; prime family must not
    # close it, and our wider searches are reported for what they are.
    r10395 = certificate(10395)
    print(f"control N=10395 (paper straggler): verdict = {r10395['verdict']}, "
          f"prime-family margin = {fmt(r10395['prime_family']['margin'])}, "
          f"best margin = {fmt(r10395['best_margin'])} with T = {r10395['best_T']}")
    ok &= r10395["prime_family"]["margin"] <= 0
    # Target sanity: 945 must be excluded (paper Table 1).
    r945 = certificate(945)
    print(f"target N=945: verdict = {r945['verdict']} (expected EXCLUDED_BY_CRT)")
    ok &= r945["verdict"] == "EXCLUDED_BY_CRT"
    print(f"SELFTEST {'OK' if ok else 'FAILED'}")
    return 0 if ok else 1


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--n", type=int, default=None)
    ap.add_argument("--all", action="store_true", help="run 945, 1575, 2205")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args(argv)
    if args.selftest:
        return selftest()
    targets = []
    if args.all:
        targets = [945, 1575, 2205]
    if args.n is not None:
        targets = [args.n]
    if not targets:
        ap.error("give --n, --all or --selftest")
    for n in targets:
        report(certificate(n))
    return 0


if __name__ == "__main__":
    sys.exit(main())
