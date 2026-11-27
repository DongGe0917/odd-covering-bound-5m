#!/usr/bin/env python3
"""
Erdos-Selfridge covering system (Erdos #7): search skeleton.

Components
----------
(a) Density sieve: for a candidate lcm N, compute S(N) = sum_{d | N, d > 1, d odd} 1/d
    in exact rational arithmetic. If S(N) < 1 no subset of the divisor pool can cover Z,
    so N is excluded. (S(N) >= 1  iff  sigma(N) >= 2N for odd N.)
(b) Backtracking search with capacity pruning on Z/NZ: decide whether some choice of
    residue classes, one per modulus from a pool of distinct divisors of N, covers all
    N residues. Pruning: at every node, sum over unused moduli m of (N/m) -- an upper
    bound on how many *new* residues they can still cover -- must be >= #uncovered.
    A node budget guards against explosion; exhausting it reports INCONCLUSIVE,
    never a false exclusion.
(c) Independent verifier: given explicit classes (a_i, m_i), check by enumeration
    over one full period L = lcm(m_i) that every residue is covered, moduli distinct.

Usage
-----
    python3 search.py verify-classic          # sanity: classic even-modulus cover + verifier
    python3 search.py sieve --limit 3000      # odd N <= limit passing the density sieve
    python3 search.py exclude --limit 944     # reproduce: no odd distinct cover with lcm <= limit
    python3 search.py search --n 945 --budget 300000   # backtracking decision for one N
    python3 search.py search --n 12 --pool all         # sanity: finds the classic cover (even moduli)
"""

import argparse
import sys
from fractions import Fraction
from math import gcd


# ---------------------------------------------------------------- utilities

def lcm(a, b):
    return a // gcd(a, b) * b


def divisors_gt1(n, odd_only=True):
    """All divisors d of n with d > 1 (and d odd if odd_only)."""
    out = []
    d = 2
    divs = set()
    i = 1
    while i * i <= n:
        if n % i == 0:
            divs.add(i)
            divs.add(n // i)
        i += 1
    for d in sorted(divs):
        if d > 1 and (not odd_only or d % 2 == 1):
            out.append(d)
    return out


def sigma(n):
    s = 0
    i = 1
    while i * i <= n:
        if n % i == 0:
            s += i
            if i != n // i:
                s += n // i
        i += 1
    return s


# ---------------------------------------------------------------- (a) sieve

def density_sum(n, odd_only=True):
    """Exact sum_{d | n, d > 1} 1/d as a Fraction."""
    return sum((Fraction(1, d) for d in divisors_gt1(n, odd_only=odd_only)), Fraction(0))


def sieve_pass(n, odd_only=True):
    return density_sum(n, odd_only=odd_only) >= 1


# ---------------------------------------------------------------- (c) verifier

def verify(classes):
    """
    classes: iterable of (a, m). Returns (ok, info).
    Checks: m > 1, moduli pairwise distinct, and every residue mod L=lcm(m_i) covered.
    """
    classes = [(a % m, m) for (a, m) in classes]
    moduli = [m for (_, m) in classes]
    if any(m <= 1 for m in moduli):
        return False, "a modulus is <= 1"
    if len(set(moduli)) != len(moduli):
        return False, "moduli are not distinct"
    L = 1
    for m in moduli:
        L = lcm(L, m)
    covered = bytearray(L)
    for (a, m) in classes:
        for x in range(a, L, m):
            covered[x] = 1
    if all(covered):
        return True, f"covers Z (period L={L}, {len(classes)} classes)"
    missing = [x for x in range(L) if not covered[x]]
    return False, f"does not cover: {len(missing)} residues mod {L} uncovered, e.g. {missing[:10]}"


# ---------------------------------------------------------------- (b) search

def search_cover(n, pool=None, odd_only=True, node_budget=200_000):
    """
    Decide whether Z/nZ can be covered by classes with distinct moduli from `pool`
    (default: divisors of n that are > 1, odd if odd_only).

    Returns (status, detail):
      status = "COVER"        -> detail is the list of (a, m) classes found
      status = "EXCLUDED"     -> search tree exhausted: no cover with moduli | n from pool
      status = "INCONCLUSIVE" -> node budget exhausted (NOT an exclusion)
    """
    if pool is None:
        pool = divisors_gt1(n, odd_only=odd_only)
    pool = sorted(pool)
    # masks[m][r] = bitmask over Z/nZ of the class r mod m
    masks = {}
    for m in pool:
        full = (1 << n) - 1
        per = []
        for r in range(m):
            bits = 0
            for x in range(r, n, m):
                bits |= 1 << x
            per.append(bits)
        masks[m] = per

    nodes = [0]
    aborted = [False]

    # capacity[m] = n // m  (number of residues one class mod m covers in Z/nZ)
    def rec(uncovered, unused, chosen):
        if uncovered == 0:
            return chosen
        if nodes[0] >= node_budget:
            aborted[0] = True
            return None
        nodes[0] += 1
        # capacity pruning: even using every unused modulus perfectly (no overlap)
        # we must be able to cover the still-uncovered residues.
        need = bin(uncovered).count("1")
        cap = sum(n // m for m in unused)
        if cap < need:
            return None
        # pick the lowest uncovered residue; branch over which modulus covers it
        x = (uncovered & -uncovered).bit_length() - 1
        # try larger classes first (smaller modulus = more coverage)
        for m in sorted(unused, key=lambda mm: -n // mm):
            r = x % m
            new_uncovered = uncovered & ~masks[m][r]
            res = rec(new_uncovered, unused - {m}, chosen + [(r, m)])
            if res is not None:
                return res
            if aborted[0]:
                return None
        return None

    full = (1 << n) - 1
    result = rec(full, frozenset(pool), [])
    if result is not None:
        return "COVER", {"classes": result, "nodes": nodes[0]}
    if aborted[0]:
        return "INCONCLUSIVE", {"nodes": nodes[0], "budget": node_budget}
    return "EXCLUDED", {"nodes": nodes[0]}


# ---------------------------------------------------------------- CLI

CLASSIC = [(0, 2), (0, 3), (1, 4), (5, 6), (7, 12)]


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    sub.add_parser("verify-classic")

    p = sub.add_parser("sieve")
    p.add_argument("--limit", type=int, default=3000)

    p = sub.add_parser("exclude")
    p.add_argument("--limit", type=int, default=944)

    p = sub.add_parser("search")
    p.add_argument("--n", type=int, required=True)
    p.add_argument("--budget", type=int, default=200_000)
    p.add_argument("--pool", choices=["odd", "all"], default="odd")

    args = ap.parse_args(argv)

    if args.cmd == "verify-classic":
        ok, info = verify(CLASSIC)
        print(f"classic system {CLASSIC}: verify -> {ok}: {info}")
        # negative control: drop the last class
        ok2, info2 = verify(CLASSIC[:-1])
        print(f"classic minus last class: verify -> {ok2}: {info2}")
        # search sanity on n=12 with all divisors (even allowed) must find a cover
        status, detail = search_cover(12, odd_only=False)
        print(f"search_cover(12, pool=all divisors>1) -> {status}: {detail}")
        if status == "COVER":
            ok3, info3 = verify(detail["classes"])
            print(f"  found classes re-verified independently -> {ok3}: {info3}")
        return 0

    if args.cmd == "sieve":
        passing = []
        for n in range(3, args.limit + 1, 2):
            if sieve_pass(n):
                passing.append(n)
        print(f"odd N <= {args.limit} passing density sieve (sum_{{d|N,d>1}} 1/d >= 1): {passing}")
        for n in passing[:10]:
            print(f"  N={n}: density sum = {density_sum(n)} = {float(density_sum(n)):.6f}, "
                  f"sigma(N)={sigma(n)}, 2N={2*n}, 9|N: {n % 9 == 0}, 15|N: {n % 15 == 0}")
        return 0

    if args.cmd == "exclude":
        bad = []
        checked = 0
        for n in range(3, args.limit + 1, 2):
            checked += 1
            if sieve_pass(n):
                bad.append(n)
        print(f"checked {checked} odd N in [3, {args.limit}]: passing sieve = {bad}")
        if not bad:
            print(f"RESULT: no odd distinct-modulus covering system has lcm <= {args.limit} "
                  f"(any such lcm is odd, its moduli divide it, and every odd N <= {args.limit} "
                  f"fails the density sieve).")
        return 0

    if args.cmd == "search":
        odd_only = args.pool == "odd"
        status, detail = search_cover(args.n, odd_only=odd_only, node_budget=args.budget)
        print(f"search_cover(N={args.n}, pool={args.pool} divisors>1, budget={args.budget}) "
              f"-> {status}: {detail}")
        if status == "COVER":
            ok, info = verify(detail["classes"])
            print(f"  classes re-verified independently -> {ok}: {info}")
        return 0

    return 1


if __name__ == "__main__":
    sys.exit(main())
