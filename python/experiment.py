# The filler-cell experiment: for every blocked shape (no cell can be the last one
# added), look for a formula that never holds more than ONE cell outside the shape.
import json, time, sys
from collections import Counter
from search import astar, lean_ops
from check import builds

blocked = json.load(open("blocked_upto_14.json"))
results = []
t0 = time.time()
for P in blocked:
    P = [tuple(c) for c in P]
    t = time.time()
    f = astar(P, allowed_extra=1)
    if f is None:  # a few shapes need a bigger search budget
        f = astar(P, allowed_extra=1, weight=1.5, max_states=6_000_000)
    ok = f is not None and builds(f, P)
    results.append({"shape": P, "n": len(P), "found": f is not None, "verified": ok,
                    "formula": None if f is None else [f[0], f[1], f[2]],
                    "steps": None if f is None else len(f[2]), "seconds": round(time.time() - t, 2)})
json.dump(results, open("experiment_results.json", "w"))
by_n = {}
for r in results: by_n.setdefault(r["n"], []).append(r)
for n in sorted(by_n):
    rs = by_n[n]
    found = [r for r in rs if r["found"]]
    print(f"N={n}: {len(rs)} blocked shapes, one filler cell works for {len(found)}, "
          f"all checked by sim.py: {all(r['verified'] for r in found)}, "
          f"steps {min(r['steps'] for r in found)}-{max(r['steps'] for r in found)}" if found else f"N={n}: none found")
print(f"total {time.time() - t0:.0f}s")
