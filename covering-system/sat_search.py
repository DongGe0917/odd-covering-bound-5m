#!/usr/bin/env python3
"""
Phase 2: SAT encoding for the Erdos-Selfridge odd covering problem (Erdos #7).

For a fixed odd candidate N (the hypothetical lcm of a covering system), decide:

    Does there exist a choice of at most one residue class per modulus m,
    where m runs over the divisors of N with m > 1 (all odd, since N is odd),
    such that the chosen classes cover every residue of Z/NZ?

Encoding (z3):
  * Variable x[m][r] (Bool) for each divisor m > 1 of N and each r in [0, m):
    "the class r mod m is chosen".
  * At most one class per modulus:  PbLe([(x[m][r], 1) for r], 1).
  * Covering: for each residue z in [0, N):  Or over m of x[m][z mod m].
  * Redundant counting constraint (implied by covering, added for propagation):
    y[m] <-> Or_r x[m][r];  PbGe([(y[m], N//m)], N).

Why this decides the right statement: if a covering system with distinct odd
moduli has lcm L, then all its moduli divide L, so it is a solution of the
instance for N = L. Hence UNSAT for every sieve-passing N <= X proves
"no odd distinct-modulus covering system has lcm <= X" (non-sieve-passing N
are already excluded by the density argument, phase 1). The encoding does NOT
require lcm(chosen moduli) = N: a SAT solution whose moduli have lcm L | N is
still a genuine covering system (a counterexample to the conjecture!) and is
re-checked with the independent verifier in search.py.

Optional translation symmetry breaking (--symbreak): covering systems are
invariant under a global shift z -> z + t. When 3 | N (true for all sieve
candidates, since 9 | N or 15 | N), modulus 3 is in the pool, and any covering
either uses modulus 3 -- then a shift makes its class 0 mod 3 -- or does not
use modulus 3 at all. So UNSAT of both cases
    (A) x[3][0] = True,  (B) all x[3][r] = False
implies UNSAT of the plain instance. SAT in either case is a real solution.

Every run writes a JSON record into results/ (encoding size, solver verdict,
wall time, z3 statistics, z3 version) so results are auditable. A z3 UNSAT is
a solver verdict, NOT a Lean kernel certificate; see 进展-02.md for the gap.

Usage (use the shared venv python):
    venv/bin/python sat_search.py one --n 945 --timeout 300
    venv/bin/python sat_search.py batch --limit 10000 --timeout 300
    venv/bin/python sat_search.py candidates --limit 30000
    venv/bin/python sat_search.py push --from 10000 --to 30000 --timeout 180
"""

import argparse
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from search import divisors_gt1, sieve_pass, verify  # noqa: E402

RESULTS_DIR = Path(__file__).resolve().parent / "results"


def sigma_sieve(limit):
    """sigma(n) for all n <= limit via divisor summatory sieve."""
    sig = [0] * (limit + 1)
    for d in range(1, limit + 1):
        for multiple in range(d, limit + 1, d):
            sig[multiple] += d
    return sig


def candidates_upto(limit, lo=3):
    """Odd N in [lo, limit] passing the density sieve: sigma(N) >= 2N."""
    sig = sigma_sieve(limit)
    return [n for n in range(max(lo, 3), limit + 1, 2) if sig[n] >= 2 * n]


def build_instance(z3, N, extra_assertions=None):
    """Build the z3 solver for candidate N. Returns (solver, x, pool)."""
    pool = divisors_gt1(N, odd_only=True)
    x = {}
    for m in pool:
        for r in range(m):
            x[(m, r)] = z3.Bool(f"x_{m}_{r}")
    s = z3.Solver()
    # at most one class per modulus
    for m in pool:
        s.add(z3.PbLe([(x[(m, r)], 1) for r in range(m)], 1))
    # covering clauses
    for z in range(N):
        s.add(z3.Or([x[(m, z % m)] for m in pool]))
    # redundant counting constraint via y[m] = "modulus m is used"
    terms = []
    for m in pool:
        y = z3.Bool(f"y_{m}")
        s.add(y == z3.Or([x[(m, r)] for r in range(m)]))
        terms.append((y, N // m))
    s.add(z3.PbGe(terms, N))
    if extra_assertions:
        for a in extra_assertions(x, pool):
            s.add(a)
    return s, x, pool


def extract_classes(model, x, pool):
    classes = []
    for m in pool:
        for r in range(m):
            v = model.eval(x[(m, r)], model_completion=True)
            import z3 as _z3
            if _z3.is_true(v):
                classes.append((r, m))
    return classes


def solve_one(N, timeout_s=300, symbreak=False, save=True, tag=""):
    import z3

    record = {
        "N": N,
        "timeout_s": timeout_s,
        "symbreak": symbreak,
        "z3_version": z3.get_version_string(),
        "started": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
    }
    t0 = time.time()

    cases = [("plain", None)]
    if symbreak:
        def case_a(x, pool):
            return [x[(3, 0)]] if 3 in pool else []
        def case_b(x, pool):
            return [z3.Not(x[(3, r)]) for r in range(3)] if 3 in pool else []
        cases = [("A: class 0 mod 3 used", case_a), ("B: modulus 3 unused", case_b)]

    case_results = []
    overall = "UNSAT"  # for symbreak: UNSAT only if every case UNSAT
    found_classes = None
    for name, extra in cases:
        s, x, pool = build_instance(z3, N, extra_assertions=extra)
        s.set(timeout=int(timeout_s * 1000))
        ct0 = time.time()
        verdict = s.check()
        cdt = time.time() - ct0
        stats = {}
        try:
            st = s.statistics()
            stats = {k: str(st.get_key_value(k)) for k in st.keys()}
        except Exception:
            pass
        entry = {"case": name, "verdict": str(verdict), "seconds": round(cdt, 3), "stats": stats}
        if verdict == z3.sat:
            found_classes = extract_classes(s.model(), x, pool)
            entry["classes"] = found_classes
            overall = "SAT"
            case_results.append(entry)
            break
        elif verdict == z3.unknown:
            entry["reason"] = str(s.reason_unknown())
            overall = "UNKNOWN"
            case_results.append(entry)
            break
        case_results.append(entry)

    dt = time.time() - t0
    pool = divisors_gt1(N, odd_only=True)
    record.update({
        "pool_size": len(pool),
        "n_vars": sum(pool),
        "verdict": overall,
        "seconds_total": round(dt, 3),
        "cases": case_results,
    })
    if found_classes is not None:
        ok, info = verify(found_classes)
        record["found_classes"] = found_classes
        record["verify_ok"] = ok
        record["verify_info"] = info
    if save:
        RESULTS_DIR.mkdir(exist_ok=True)
        fname = RESULTS_DIR / f"sat_N{N}{tag}.json"
        with open(fname, "w") as f:
            json.dump(record, f, indent=1, ensure_ascii=False)
        record["record_file"] = str(fname)
    return record


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("one")
    p.add_argument("--n", type=int, required=True)
    p.add_argument("--timeout", type=int, default=300)
    p.add_argument("--symbreak", action="store_true")

    p = sub.add_parser("batch")
    p.add_argument("--limit", type=int, default=10000)
    p.add_argument("--timeout", type=int, default=300)
    p.add_argument("--symbreak", action="store_true")

    p = sub.add_parser("candidates")
    p.add_argument("--limit", type=int, default=30000)

    p = sub.add_parser("push")
    p.add_argument("--frm", type=int, default=10000)
    p.add_argument("--to", type=int, default=30000)
    p.add_argument("--timeout", type=int, default=180)
    p.add_argument("--symbreak", action="store_true")

    args = ap.parse_args(argv)

    if args.cmd == "candidates":
        cands = candidates_upto(args.limit)
        print(f"odd N <= {args.limit} passing density sieve: {len(cands)}")
        print(cands)
        return 0

    if args.cmd == "one":
        rec = solve_one(args.n, timeout_s=args.timeout, symbreak=args.symbreak)
        print(json.dumps({k: rec[k] for k in ("N", "pool_size", "n_vars", "verdict", "seconds_total")}, ensure_ascii=False))
        for c in rec["cases"]:
            print(f"  case {c['case']}: {c['verdict']} in {c['seconds']}s")
        if rec["verdict"] == "SAT":
            print(f"  !!! SAT: classes={rec.get('found_classes')}")
            print(f"  independent verify -> {rec.get('verify_ok')}: {rec.get('verify_info')}")
        return 0

    if args.cmd in ("batch", "push"):
        if args.cmd == "batch":
            cands = candidates_upto(args.limit)
        else:
            cands = [n for n in candidates_upto(args.to) if n > args.frm]
        print(f"{len(cands)} candidates to attempt: {cands}", flush=True)
        summary = []
        for n in cands:
            rec = solve_one(n, timeout_s=args.timeout, symbreak=args.symbreak)
            line = {"N": n, "verdict": rec["verdict"], "seconds": rec["seconds_total"]}
            summary.append(line)
            print(line, flush=True)
            if rec["verdict"] == "SAT":
                print(f"  !!! SAT at N={n}: verify -> {rec.get('verify_ok')}: {rec.get('verify_info')}", flush=True)
                break
        out = RESULTS_DIR / f"summary_{args.cmd}_{int(time.time())}.json"
        RESULTS_DIR.mkdir(exist_ok=True)
        with open(out, "w") as f:
            json.dump(summary, f, indent=1)
        print(f"summary written to {out}")
        return 0

    return 1


if __name__ == "__main__":
    sys.exit(main())
