#!/usr/bin/env python3
"""
Phase 2, second engine: CNF encoding + Glucose (python-sat) for the same
fixed-N covering decision problem as sat_search.py (see that file's docstring
for why UNSAT for all sieve candidates <= X proves the lcm bound).

Encoding:
  * one Bool var per (modulus m | N, m > 1; residue r in [0, m));
  * covering clause per residue z of Z/NZ: Or_m x[m][z mod m];
  * at-most-one per modulus via CardEnc sequential counter (bound=1);
  * optional translation symmetry breaking (--symbreak), same two-case split
    as sat_search.py: (A) class 0 mod 3 used, (B) modulus 3 unused.

Timeout is enforced with a threading.Timer calling solver.interrupt()
(python-sat's solve_limited). Verdicts: UNSAT / SAT / UNKNOWN(timeout).
A SAT model is mapped back to classes and re-checked with the independent
verifier from search.py. Records are written as JSON into results/.

Usage:
    venv/bin/python cnf_search.py one --n 10395 --timeout 300 [--symbreak]
    venv/bin/python cnf_search.py queue --timeout 300 [--symbreak]
        (queue = the CRT-PASS candidates in (10000, 30000] plus any listed)
"""

import argparse
import json
import sys
import threading
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from search import divisors_gt1, verify  # noqa: E402

RESULTS_DIR = Path(__file__).resolve().parent / "results"


def build_cnf(N):
    """Returns (clauses, var_of, pool, n_aux) with variables numbered from 1."""
    from pysat.card import CardEnc, EncType

    pool = divisors_gt1(N, odd_only=True)
    var_of = {}
    nxt = 1
    for m in pool:
        for r in range(m):
            var_of[(m, r)] = nxt
            nxt += 1
    clauses = []
    # covering clauses
    for z in range(N):
        clauses.append([var_of[(m, z % m)] for m in pool])
    # at-most-one per modulus (sequential counter, introduces aux vars)
    top = nxt - 1
    for m in pool:
        lits = [var_of[(m, r)] for r in range(m)]
        enc = CardEnc.atmost(lits=lits, bound=1, top_id=top, encoding=EncType.seqcounter)
        clauses.extend(enc.clauses)
        top = enc.nv
    return clauses, var_of, pool, top


def solve_one(N, timeout_s=300, symbreak=False, save=True):
    from pysat.solvers import Glucose4

    record = {
        "N": N, "engine": "glucose4-cnf", "timeout_s": timeout_s,
        "symbreak": symbreak, "started": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
    }
    t0 = time.time()
    clauses, var_of, pool, nv = build_cnf(N)
    record.update({"pool_size": len(pool), "n_vars_total": nv,
                   "n_clauses": len(clauses), "build_seconds": round(time.time() - t0, 3)})

    cases = [("plain", [])]
    if symbreak and 3 in pool:
        cases = [("A: class 0 mod 3 used", [[var_of[(3, 0)]]]),
                 ("B: modulus 3 unused", [[-var_of[(3, r)]] for r in range(3)])]

    overall = "UNSAT"
    case_results = []
    found = None
    for name, units in cases:
        s = Glucose4(bootstrap_with=clauses + units)
        timer = threading.Timer(timeout_s, s.interrupt)
        ct0 = time.time()
        timer.start()
        res = s.solve_limited(expect_interrupt=True)
        timer.cancel()
        cdt = time.time() - ct0
        if res is None:
            verdict = "UNKNOWN"
        elif res:
            verdict = "SAT"
        else:
            verdict = "UNSAT"
        entry = {"case": name, "verdict": verdict, "seconds": round(cdt, 3)}
        if verdict == "SAT":
            model = set(s.get_model())
            found = [(r, m) for m in pool for r in range(m) if var_of[(m, r)] in model]
            entry["classes"] = found
            overall = "SAT"
            case_results.append(entry)
            s.delete()
            break
        if verdict == "UNKNOWN":
            overall = "UNKNOWN"
            case_results.append(entry)
            s.delete()
            break
        case_results.append(entry)
        s.delete()

    record["verdict"] = overall
    record["seconds_total"] = round(time.time() - t0, 3)
    record["cases"] = case_results
    if found is not None:
        ok, info = verify(found)
        record["found_classes"] = found
        record["verify_ok"] = ok
        record["verify_info"] = info
    if save:
        RESULTS_DIR.mkdir(exist_ok=True)
        fname = RESULTS_DIR / f"cnf_N{N}.json"
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
    p = sub.add_parser("queue")
    p.add_argument("--ns", type=int, nargs="*", default=[10395, 12285, 17325, 20475, 24255, 26775])
    p.add_argument("--timeout", type=int, default=300)
    p.add_argument("--symbreak", action="store_true")
    args = ap.parse_args(argv)

    if args.cmd == "one":
        rec = solve_one(args.n, timeout_s=args.timeout, symbreak=args.symbreak)
        print({k: rec[k] for k in ("N", "pool_size", "n_vars_total", "n_clauses", "verdict", "seconds_total")}, flush=True)
        if rec["verdict"] == "SAT":
            print(f"  !!! SAT classes={rec.get('found_classes')} verify -> {rec.get('verify_ok')}: {rec.get('verify_info')}", flush=True)
        return 0
    if args.cmd == "queue":
        for n in args.ns:
            rec = solve_one(n, timeout_s=args.timeout, symbreak=args.symbreak)
            print({"N": n, "verdict": rec["verdict"], "seconds": rec["seconds_total"]}, flush=True)
            if rec["verdict"] == "SAT":
                print(f"  !!! SAT at N={n}: verify -> {rec.get('verify_ok')}: {rec.get('verify_info')}", flush=True)
                break
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
