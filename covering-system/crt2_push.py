#!/usr/bin/env python3
"""
Push the continuous lower bound beyond 100000 with the level-2 certificate.

Candidates are odd N passing the density sieve: a covering's lcm L must
satisfy sum_{d | L, d > 1} 1/d >= 1, i.e. sigma(L)/L - 1 >= 1, i.e.
sigma(L) >= 2L (L odd abundant).  sigma is computed by an exact integer
sieve (no floats).  Consistency gate: the sieve must reproduce exactly the
210 candidates <= 100000 recorded in results/crt_batch_*.jsonl before any
new range is trusted.

For each new candidate, families T are tried in the order prime family ->
prime-power choice -> exhaustive pairwise-coprime subsets, with early exit
on the first positive refined margin (one firing T suffices for exclusion).
If nothing fires, the best margin over the completed search is recorded
and the verdict is PASS (honest non-exclusion).

Usage: python3 crt2_push.py --limit 1000000
"""

import argparse
import json
import sys
import time
from fractions import Fraction

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from search import divisors_gt1  # noqa: E402
from crt2_capacity import refined_margin, _search_families  # noqa: E402


def odd_abundant_sieve(limit):
    """All odd N <= limit with sigma(N) >= 2N, via exact integer sieve."""
    sigma = [0] * (limit + 1)
    for d in range(1, limit + 1):
        for m in range(d, limit + 1, d):
            sigma[m] += d
    return [n for n in range(3, limit + 1, 2) if sigma[n] >= 2 * n]


def certificate2_fast(n, node_limit=2_000_000):
    """
    Level-2 exclusion with early exit.  Returns dict with verdict,
    firing/best T, margin, families_checked, search_completed.
    """
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
        if m > 0:
            return {"verdict": "EXCLUDED_BY_CRT2", "T": T, "margin": m,
                    "families_checked": checked, "search_completed": completed}
    return {"verdict": "PASS", "T": best_T, "margin": best_margin,
            "families_checked": checked, "search_completed": completed}


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--limit", type=int, default=1_000_000)
    ap.add_argument("--out", default=None)
    args = ap.parse_args(argv)
    out_path = args.out or f"results/crt2_batch_100001_{args.limit}.jsonl"

    t0 = time.perf_counter()
    cands = odd_abundant_sieve(args.limit)
    print(f"sieve to {args.limit}: {len(cands)} odd abundant candidates "
          f"({time.perf_counter() - t0:.1f} s)")

    # consistency gate vs phase-2 records <= 100000
    known = set()
    for fn in ("results/crt_batch_le10000.jsonl",
               "results/crt_batch_10001_30000.jsonl",
               "results/crt_batch_30001_100000.jsonl"):
        with open(fn) as fh:
            for line in fh:
                known.add(json.loads(line)["N"])
    mine = {n for n in cands if n <= 100_000}
    print(f"consistency <=100000: sieve {len(mine)} vs recorded {len(known)}, "
          f"identical = {mine == known}")
    if mine != known:
        print("MISMATCH -- aborting push; sieve definition differs.")
        return 1

    new = [n for n in cands if n > 100_000]
    print(f"new candidates in (100000, {args.limit}]: {len(new)}")
    excluded = 0
    first_pass = None
    with open(out_path, "w") as fh:
        for i, n in enumerate(new):
            res = certificate2_fast(n)
            row = {"N": n, "verdict": res["verdict"],
                   "T": list(res["T"]) if res["T"] else None,
                   "margin": str(res["margin"]),
                   "families_checked": res["families_checked"],
                   "search_completed": res["search_completed"]}
            fh.write(json.dumps(row) + "\n")
            fh.flush()
            if res["verdict"] == "EXCLUDED_BY_CRT2":
                excluded += 1
            elif first_pass is None:
                first_pass = n
                print(f"  first PASS at N={n}: best margin {res['margin']} "
                      f"(~{float(res['margin']):.6f}), T={res['T']}, "
                      f"completed={res['search_completed']}")
            if (i + 1) % 250 == 0:
                print(f"  ... {i + 1}/{len(new)} processed, "
                      f"{excluded} excluded, "
                      f"{time.perf_counter() - t0:.0f} s elapsed")
    print(f"done: {excluded}/{len(new)} new candidates excluded; "
          f"first PASS = {first_pass}; total {time.perf_counter() - t0:.0f} s")
    if first_pass is None:
        print(f"CONTINUOUS BOUND: no odd distinct-moduli covering with "
              f"lcm <= {args.limit} (all candidates excluded, rest by density)")
    else:
        print(f"CONTINUOUS BOUND: lcm <= {first_pass - 1} "
              f"(breakpoint {first_pass})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
