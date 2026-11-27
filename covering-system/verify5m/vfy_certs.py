#!/usr/bin/env python3
"""
Independent certificate re-verification.

For every exclusion record in the executor's results files, recompute the
margin from the recorded certificate parameters using MY OWN implementations
of the capacity formulas, derived from the mathematical definitions:

Level 1 (forcers T pairwise coprime; patches bounded crudely by N/d):
    margin1(N,T) = prod_{t in T} (1 - 1/t)  -  sum_{d in pool, d notin T} 1/d
    exclusion iff margin1 > 0.

Level 2 (exact max intersection of a patch class with the forced-uncovered
set A_U; normalised condition is monotone in U, worst case U = T):
    margin2(N,T) = 1 - sum_{d in pool, d notin T} (1/d)
                       * prod_{t in T, gcd(d,t) > 1} t/(t-1)
    exclusion iff margin2 > 0.

Level 3 (forcers F = prime powers, not necessarily coprime; per-prime exact
local ratios rho_bar_p(f) = max over local configurations gamma of
max_c |A_gamma cap (c mod p^f)| / |A_gamma|, configurations enumerated by
brute force over subsets of F_p with all residue choices):
    margin3(N,F) = 1 - sum_{d in pool, d notin F} prod_p rho_bar_p(v_p(d))
    exclusion iff margin3 > 0.

Also validates certificate well-formedness (T: divisors of N, pairwise
coprime; F: prime powers dividing N), cross-file consistency for duplicated
N, and final coverage: every candidate from my own sieve must own at least
one record whose RECOMPUTED margin is > 0.
"""
import json
import time
from fractions import Fraction
from math import gcd
from pathlib import Path

from vfy_common import divisors_of, factorize, primes_upto

HERE = Path(__file__).resolve().parent
RESULTS = HERE.parent / "results"
PRIMES = primes_upto(100000)


# ---------------------------------------------------------------- formulas
def margin1(n, T):
    fac = factorize(n, PRIMES)
    pool = [d for d in divisors_of(fac) if d > 1]
    prod = Fraction(1)
    for t in T:
        prod *= Fraction(t - 1, t)
    s = sum((Fraction(1, d) for d in pool if d not in T), Fraction(0))
    return prod - s


def margin2(n, T):
    fac = factorize(n, PRIMES)
    pool = [d for d in divisors_of(fac) if d > 1]
    total = Fraction(0)
    for d in pool:
        if d in T:
            continue
        term = Fraction(1, d)
        for t in T:
            if gcd(d, t) > 1:
                term *= Fraction(t, t - 1)
        total += term
    return 1 - total


def rho_bar_for_prime(p, e, Fp):
    """rho_bar_p(f) for f = 0..e by brute-force local configuration search.

    Fp: list of exponents f (1<=f<=e) whose prime power p^f is a forcer.
    A configuration gamma = choice, for each f in Fp, of 'unused' or a
    residue a mod p^f.  A_gamma = residues mod p^e avoiding all chosen
    classes.  rho_bar(f) = max_gamma  max_c |A_gamma cap (c mod p^f)|/|A_gamma|.
    """
    mod = p ** e
    full = (1 << mod) - 1

    def class_mask(f, a):
        m = 0
        step = p ** f
        for x in range(a, mod, step):
            m |= 1 << x
        return m

    masks = {f: [class_mask(f, a) for a in range(p ** f)] for f in range(e + 1)}
    rho = [Fraction(1)] + [Fraction(0)] * e
    seen_A = set()
    # enumerate configurations recursively over Fp
    stack = [(0, 0)]  # (index into Fp, OR of forbidden-class masks)
    while stack:
        i, forb = stack.pop()
        if i == len(Fp):
            A = full ^ forb
            if A in seen_A:
                continue
            seen_A.add(A)
            cnt = bin(A).count("1")
            assert cnt > 0, f"empty A_gamma for p={p}, e={e}, Fp={Fp}"
            for f in range(1, e + 1):
                g = 0
                for c in range(p ** f):
                    v = bin(A & masks[f][c]).count("1")
                    if v > g:
                        g = v
                r = Fraction(g, cnt)
                if r > rho[f]:
                    rho[f] = r
            continue
        f = Fp[i]
        stack.append((i + 1, forb))  # forcer p^f unused
        for a in range(p ** f):
            stack.append((i + 1, forb | masks[f][a]))
    return rho


def margin3(n, F):
    fac = factorize(n, PRIMES)
    rho = {}
    for p, e in fac.items():
        Fp = [f for f in range(1, e + 1) if p ** f in F]
        rho[p] = rho_bar_for_prime(p, e, Fp)
    total = Fraction(0)
    # generate divisors together with their exponent vectors
    items = sorted(fac.items())

    def gen(i, d, exps):
        if i == len(items):
            yield d, exps
            return
        p, e = items[i]
        pw = 1
        for f in range(e + 1):
            yield from gen(i + 1, d * pw, exps + [(p, f)])
            pw *= p

    for d, exps in gen(0, 1, []):
        if d == 1 or d in F:
            continue
        term = Fraction(1)
        for p, f in exps:
            if f:
                term *= rho[p][f]
        total += term
    return 1 - total, rho


# ---------------------------------------------------------------- validity
def check_T(n, T):
    fac = factorize(n, PRIMES)
    divs = set(divisors_of(fac))
    if any(t not in divs or t <= 1 for t in T):
        return "T element not a divisor > 1 of N"
    for i in range(len(T)):
        for j in range(i + 1, len(T)):
            if gcd(T[i], T[j]) != 1:
                return "T not pairwise coprime"
    return None


def check_F(n, F):
    fac = factorize(n, PRIMES)
    for q in F:
        fq = factorize(q, PRIMES)
        if len(fq) != 1:
            return f"F element {q} not a prime power"
        p, f = next(iter(fq.items()))
        if fac.get(p, 0) < f:
            return f"F element {q} does not divide N"
    return None


# ---------------------------------------------------------------- driver
def load_jsonl(name):
    out = []
    for line in open(RESULTS / name):
        line = line.strip()
        if line:
            out.append(json.loads(line))
    return out


def main():
    t0 = time.time()
    problems = []
    stats = {"L1_checked": 0, "L1_match": 0, "L2_checked": 0, "L2_match": 0,
             "L3_checked": 0, "L3_match": 0}
    verified_exclusion = {}   # N -> list of levels with recomputed margin > 0
    detail = open(HERE / "cert_recheck_detail.jsonl", "w")

    def note(N, level, ok, extra=""):
        detail.write(json.dumps({"N": N, "level": level, "ok": ok,
                                 "extra": extra}) + "\n")

    # ---- level 1
    for name in ["crt_batch_le10000.jsonl", "crt_batch_10001_30000.jsonl",
                 "crt_batch_30001_100000.jsonl"]:
        for r in load_jsonl(name):
            n, T = r["N"], r["best_T"]
            err = check_T(n, T)
            m = margin1(n, T)
            recorded = Fraction(r["best_margin"])
            stats["L1_checked"] += 1
            ok = (err is None and m == recorded
                  and (m > 0) == (r["verdict"] == "EXCLUDED_BY_CRT"))
            if ok:
                stats["L1_match"] += 1
            else:
                problems.append(f"L1 N={n} T={T}: recomputed {m} vs recorded "
                                f"{recorded}, verdict {r['verdict']}, err={err}")
            note(n, 1, ok, f"margin={m}")
            if r["verdict"] == "EXCLUDED_BY_CRT" and m > 0 and err is None:
                verified_exclusion.setdefault(n, []).append(1)

    # ---- level 2 (two record layouts; dedupe by (N, tuple(T), margin))
    l2_records = {}
    for name in ["crt2_batch_unresolved.jsonl",
                 "crt2_batch_100001_1000000.jsonl",
                 "crt2_batch_100001_5000000.jsonl"]:
        for r in load_jsonl(name):
            T = r.get("T", r.get("best_T"))
            marg = r.get("margin", r.get("best_margin"))
            key = (r["N"], tuple(T), marg)
            prev = l2_records.get(r["N"])
            if prev is not None and prev != (tuple(T), marg, r["verdict"]):
                problems.append(f"L2 cross-file inconsistency N={r['N']}: "
                                f"{prev} vs {(tuple(T), marg, r['verdict'])}")
            l2_records[r["N"]] = (tuple(T), marg, r["verdict"])
    for n, (T, marg, verdict) in sorted(l2_records.items()):
        err = check_T(n, list(T))
        m = margin2(n, list(T))
        recorded = Fraction(marg)
        stats["L2_checked"] += 1
        ok = (err is None and m == recorded
              and (m > 0) == (verdict == "EXCLUDED_BY_CRT2"))
        if ok:
            stats["L2_match"] += 1
        else:
            problems.append(f"L2 N={n} T={T}: recomputed {m} vs recorded "
                            f"{recorded}, verdict {verdict}, err={err}")
        note(n, 2, ok, f"margin={m}")
        if verdict == "EXCLUDED_BY_CRT2" and m > 0 and err is None:
            verified_exclusion.setdefault(n, []).append(2)
    print(f"L1+L2 done ({time.time()-t0:.0f}s): {stats}", flush=True)

    # ---- level 3
    l3_records = {}
    for r in load_jsonl("crt3_batch_pass5m.jsonl"):
        l3_records[r["N"]] = r
    single = json.loads(open(RESULTS / "crt3_N675675.json").read())
    if single["N"] in l3_records:
        a, b = l3_records[single["N"]], single
        if a["F"] != b["F"] or a["margin"] != b["margin"]:
            problems.append("L3 crt3_N675675.json inconsistent with batch record")
    l3_records[single["N"]] = single
    for n, r in sorted(l3_records.items()):
        F = r["F"]
        err = check_F(n, F)
        m, rho = margin3(n, F)
        recorded_m = Fraction(r["margin"])
        recorded_s = Fraction(r["sum"])
        stats["L3_checked"] += 1
        ok = (err is None and m == recorded_m and (1 - m) == recorded_s
              and m > 0)
        if "rho_bar" in r:
            for p, vec in r["rho_bar"].items():
                mine = [str(x) for x in rho[int(p)]]
                if mine != [str(Fraction(v)) for v in vec]:
                    ok = False
                    problems.append(f"L3 N={n} rho_bar[{p}]: mine {mine} "
                                    f"vs recorded {vec}")
        if ok:
            stats["L3_match"] += 1
        else:
            problems.append(f"L3 N={n} F={F}: recomputed margin {m} vs "
                            f"recorded {recorded_m}, err={err}")
        note(n, 3, ok, f"margin={m}")
        if m > 0 and err is None:
            verified_exclusion.setdefault(n, []).append(3)
    detail.close()
    print(f"L3 done ({time.time()-t0:.0f}s): {stats}", flush=True)

    # ---- final coverage against my own candidate list
    my_cands = [int(x) for x in open(HERE / "my_candidates.txt").read().split()]
    uncovered = [n for n in my_cands if n not in verified_exclusion]
    stray = [n for n in verified_exclusion if n not in set(my_cands)]
    print(f"coverage: {len(my_cands)} candidates, "
          f"{len(verified_exclusion)} with verified exclusion, "
          f"uncovered {len(uncovered)}, stray {len(stray)}")
    if uncovered:
        problems.append(f"candidates without verified exclusion: {uncovered[:20]}")
    if stray:
        problems.append(f"exclusions for non-candidates: {stray[:20]}")

    summary = {"stats": stats, "candidates": len(my_cands),
               "verified_excluded_N": len(verified_exclusion),
               "uncovered": uncovered, "stray": stray,
               "problems": problems, "seconds": round(time.time() - t0, 1)}
    with open(HERE / "cert_recheck_summary.json", "w") as f:
        json.dump(summary, f, indent=1)
    print(json.dumps(summary, indent=1)[:3000])


if __name__ == "__main__":
    main()
