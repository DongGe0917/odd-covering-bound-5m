#!/usr/bin/env python3
"""Queue driver: z3 (symbreak) on the CRT-PASS candidates in (10000, 30000].
Appends one JSON line per finished N to results/sat_queue.jsonl."""
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from sat_search import solve_one  # noqa: E402

NS = [10395, 12285, 17325, 20475, 24255, 26775]
TIMEOUT = int(sys.argv[1]) if len(sys.argv) > 1 else 600
OUT = Path(__file__).resolve().parent / "results" / "sat_queue.jsonl"

with open(OUT, "a") as f:
    for n in NS:
        t0 = time.time()
        rec = solve_one(n, timeout_s=TIMEOUT, symbreak=True, tag="_queue")
        line = {"N": n, "verdict": rec["verdict"], "seconds": rec["seconds_total"],
                "cases": [(c["case"], c["verdict"], c["seconds"]) for c in rec["cases"]]}
        print(line, flush=True)
        f.write(json.dumps(line, ensure_ascii=False) + "\n")
        f.flush()
        if rec["verdict"] == "SAT":
            print(f"!!! SAT at {n}: verify -> {rec.get('verify_ok')}: {rec.get('verify_info')}", flush=True)
            break
print("queue done", flush=True)
