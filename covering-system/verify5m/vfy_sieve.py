#!/usr/bin/env python3
"""
Independent candidate enumeration audit.

Candidate definition (derived, not copied): a covering system with distinct
moduli > 1 and odd lcm L must satisfy sum_{d in S} 1/d >= 1 for its modulus
set S (densities add to at least 1), and S is a subset of the divisors of L,
so sum_{d|L, d>1} 1/d >= 1, i.e. sigma(L)/L - 1 >= 1, i.e. sigma(L) >= 2L.
Candidates <= X := odd N <= X with sigma(N) >= 2N.

Two independent computations:
  (A) Full range <= 100000: per-number factorisation -> multiplicative sigma.
      (Completely separate code path from any bulk sieve.)
  (B) Full range <= 5,000,000: numpy divisor-sum sieve (sigma[m] += d over
      multiples), cross-validated against per-number factorisation on a
      deterministic random sample of 3000 odd n in (100000, 5e6].

Then the candidate set is compared, as a set, against the union of all N
appearing in the executor's results/*.jsonl batch files.
"""
import json
import random
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
RESULTS = HERE.parent / "results"
from vfy_common import factorize, primes_upto, sigma_of  # noqa: E402

LIMIT = 5_000_000
PRIMES = primes_upto(100000)


def candidates_by_factorisation(limit):
    out = []
    for n in range(3, limit + 1, 2):
        if sigma_of(factorize(n, PRIMES)) >= 2 * n:
            out.append(n)
    return out


def candidates_by_numpy_sieve(limit):
    sigma = np.zeros(limit + 1, dtype=np.int64)
    for d in range(1, limit + 1):
        sigma[d::d] += d
    idx = np.arange(3, limit + 1, 2)
    return idx[sigma[idx] >= 2 * idx].tolist(), sigma


def executor_candidate_union():
    files = ["crt_batch_le10000.jsonl", "crt_batch_10001_30000.jsonl",
             "crt_batch_30001_100000.jsonl", "crt2_batch_100001_1000000.jsonl",
             "crt2_batch_100001_5000000.jsonl", "crt2_batch_unresolved.jsonl",
             "crt3_batch_pass5m.jsonl"]
    union = set()
    per_file = {}
    for name in files:
        ns = set()
        for line in open(RESULTS / name):
            line = line.strip()
            if line:
                ns.add(json.loads(line)["N"])
        per_file[name] = len(ns)
        union |= ns
    extra = json.loads(open(RESULTS / "crt3_N675675.json").read())
    union.add(extra["N"])
    return union, per_file


def main():
    t0 = time.time()
    cand_a = candidates_by_factorisation(100_000)
    print(f"[A] factorisation <=100000: {len(cand_a)} candidates "
          f"({time.time()-t0:.1f}s)", flush=True)

    t0 = time.time()
    cand_b, sigma = candidates_by_numpy_sieve(LIMIT)
    print(f"[B] numpy sieve <=5e6: {len(cand_b)} candidates "
          f"({time.time()-t0:.1f}s)", flush=True)

    # cross-validate the bulk sieve on a random sample by factorisation
    rng = random.Random(20261127)
    sample = rng.sample(range(100_001, LIMIT + 1, 2), 3000)
    bad = [n for n in sample if int(sigma[n]) != sigma_of(factorize(n, PRIMES))]
    print(f"[B-sample] 3000 random odd n in (1e5,5e6]: sigma mismatches = {len(bad)}",
          flush=True)

    # the two methods must agree on the overlap range
    cand_b_small = [n for n in cand_b if n <= 100_000]
    agree_small = cand_b_small == cand_a
    print(f"[A vs B] <=100000 agreement: {agree_small}", flush=True)

    union, per_file = executor_candidate_union()
    mine = set(cand_b)
    only_mine = sorted(mine - union)
    only_theirs = sorted(union - mine)
    print(f"[union] executor records cover {len(union)} distinct N; "
          f"mine {len(mine)}; only-mine {len(only_mine)}; "
          f"only-theirs {len(only_theirs)}", flush=True)
    if only_mine:
        print("  only-mine (first 20):", only_mine[:20])
    if only_theirs:
        print("  only-theirs (first 20):", only_theirs[:20])

    report = {
        "limit": LIMIT,
        "my_candidate_count": len(cand_b),
        "my_candidate_count_le100000": len(cand_a),
        "executor_union_count": len(union),
        "executor_per_file_distinct": per_file,
        "methods_agree_le100000": agree_small,
        "sieve_sample_sigma_mismatches": len(bad),
        "only_mine": only_mine,
        "only_theirs": only_theirs,
        "sets_equal": not only_mine and not only_theirs,
    }
    with open(HERE / "sieve_diff.json", "w") as f:
        json.dump(report, f, indent=1)
    with open(HERE / "my_candidates.txt", "w") as f:
        f.write("\n".join(map(str, cand_b)))
    print(json.dumps(report, indent=1))


if __name__ == "__main__":
    sys.exit(main())
