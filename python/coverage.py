# Find a formula for EVERY fixed polyomino up to N cells.
# Tries additions only first, then allows 1, then 2 cells outside the shape.
import json, sys, time
from polys import fixed_polyominoes, normalize
from search import astar
from check import builds

N = int(sys.argv[1])
out, fails, stats = [], [], {}
t0 = time.time()
for P in fixed_polyominoes(N):
    P = normalize(P)
    for extra in (0, 1, 2):
        f = astar(P, allowed_extra=extra, allow_sub=extra > 0)
        if f: break
    n = len(P)
    s = stats.setdefault(n, {"shapes": 0, "add_only": 0, "needs_extra": 0, "not_found": 0, "max_steps": 0})
    s["shapes"] += 1
    if f is None or not builds(f, P):
        s["not_found"] += 1; fails.append(P); continue
    s["add_only" if extra == 0 else "needs_extra"] += 1
    s["max_steps"] = max(s["max_steps"], len(f[2]))
    out.append({"shape": P, "formula": [f[0], f[1], f[2]]})
json.dump(out, open(f"witnesses_upto_{N}.json", "w"))
for n in sorted(stats): print(f"N={n}: {stats[n]}")
print("not found:", fails[:5], f"\n{time.time() - t0:.0f}s")
