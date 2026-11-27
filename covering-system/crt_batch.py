#!/usr/bin/env python3
"""Batch driver: run the CRT capacity certificate over sieve candidates.

For every odd N in [lo, hi] passing the density sieve (sigma(N) >= 2N),
run crt_capacity.certificate(N). Results appended as JSON lines to a file
so an interrupted run keeps its records. Non-candidates need no work:
the density sieve already excludes them (phase 1).
"""
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from crt_capacity import certificate  # noqa: E402
from sat_search import candidates_upto  # noqa: E402


def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 10000
    out = Path(sys.argv[3]) if len(sys.argv) > 3 else Path(__file__).parent / "results" / f"crt_batch_{lo}_{hi}.jsonl"
    out.parent.mkdir(exist_ok=True)
    cands = [n for n in candidates_upto(hi) if n >= lo]
    print(f"{len(cands)} sieve candidates in [{lo},{hi}]", flush=True)
    with open(out, "a") as f:
        for n in cands:
            t0 = time.time()
            res = certificate(n)
            dt = time.time() - t0
            rec = {"N": n, "verdict": res.get("verdict"), "seconds": round(dt, 3)}
            if "best_T" in res:
                rec["best_T"] = list(res["best_T"])
            if "best_margin" in res:
                rec["best_margin"] = str(res["best_margin"])
            ex = res.get("exhaustive") or {}
            rec["exhaustive_completed"] = ex.get("completed")
            rec["exhaustive_nodes"] = ex.get("nodes")
            print(rec, flush=True)
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
            f.flush()
    print("done", flush=True)


if __name__ == "__main__":
    main()
