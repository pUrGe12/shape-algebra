# Breadth-first search for formulas, using the same rules as ShapeAlgebra.lean.
#
# Cells are kept in absolute coordinates (the rules don't care where a shape sits),
# and mirrors reflect through the axes, so we always know where each cell is relative
# to the target shape. `o` records which reflections are currently applied.

from collections import deque

def line_of(d, c): return c[1] if d == 'R' else c[0]
def along(d, c):   return c[0] if d == 'R' else c[1]
def cell_at(d, k, a): return (a, k) if d == 'R' else (k, a)

def reach(d, cs, k):
    ps = [along(d, c) for c in cs if line_of(d, c) == k]
    return max(ps) if ps else None

def step(st, op):
    cells, latch, pushed, pin, o = st
    kind, d = op
    if kind == 'push':
        return (cells, d, True, pin, o)
    if kind == 'pin':
        return (cells, latch, pushed, cells, o)
    if kind == 'mirror':
        f = (lambda p: (p[0], -p[1])) if d == 'R' else (lambda p: (-p[0], p[1]))
        o2 = (o[0], -o[1]) if d == 'R' else (-o[0], o[1])
        pin2 = None if pin is None else frozenset(map(f, pin))
        return (frozenset(map(f, cells)), latch, pushed, pin2, o2)
    # add / sub
    scope = cells if pin is None else cells & pin
    if not scope:
        return None
    lines = [line_of(latch, c) for c in scope]
    if pushed:
        count = {}
        for k in lines: count[k] = count.get(k, 0) + 1
        k = max(count, key=lambda k: (count[k], k))
    else:
        k = max(lines)
    line = k if latch == d else reach(latch, scope, k)
    a = reach(d, cells, line)
    if kind == 'add':
        cells = cells | {cell_at(d, line, a + 1)}
    else:
        cells = cells - {cell_at(d, line, a)}
    return (cells, latch, False, pin, o)

OPS = [('add', 'R'), ('add', 'C'), ('sub', 'R'), ('sub', 'C'),
       ('mirror', 'R'), ('mirror', 'C'), ('push', 'R'), ('push', 'C'), ('pin', None)]

def runs(S):
    """Every straight segment of S: candidate starting strips (dir, cells)."""
    out = []
    for d in 'RC':
        for c in S:
            seg = []
            k, a = line_of(d, c), along(d, c)
            while cell_at(d, k, a) in S:
                seg.append(cell_at(d, k, a))
                out.append((d, frozenset(seg)))
                a += 1
    return out

def search(P, allowed_extra=1, max_states=3_000_000):
    """Shortest formula that builds P exactly, never holding more than
    `allowed_extra` cells outside P. Returns (dir, j, ops) or None."""
    P = frozenset(map(tuple, P))
    def ok(cells, o):
        q = {(o[0] * x, o[1] * y) for x, y in cells}
        return len(q - P) <= allowed_extra
    start = [((cells, d, False, None, (1, 1)), (d, len(cells))) for d, cells in runs(P)]
    parent = {}
    queue = deque()
    for st, base in start:
        if st not in parent:
            parent[st] = (None, base)
            queue.append(st)
    while queue:
        st = queue.popleft()
        if st[0] == P and st[4] == (1, 1):
            ops = []
            while parent[st][0] is not None:
                prev, op = parent[st]
                ops.append(op)
                st = prev
            d, j = parent[st][1]
            return d, j, ops[::-1]
        if len(parent) > max_states:
            return None
        for op in OPS:
            nx = step(st, op)
            if nx is None or nx in parent or not ok(nx[0], nx[4]):
                continue
            parent[nx] = (st, op)
            queue.append(nx)
    return None

def lean_ops(ops):
    return "[" + ", ".join(k if d is None else f"{k} {d}" for k, d in ops) + "]"


# ---------------------------------------------------------------------------
# Faster search for bigger shapes: states packed into integers, and a guided
# (weighted A*) search that expands the states closest to the target first.
# Finds a valid formula, not necessarily the shortest.

import heapq

def astar(P, allowed_extra=1, weight=2, max_states=2_000_000, allow_sub=True):
    P = sorted(set(map(tuple, P)))
    Pset = set(P)
    # every cell that could ever be used: P and everything within distance 2
    U = sorted({(x + dx, y + dy) for x, y in P
                for dx in range(-2, 3) for dy in range(-2, 3) if abs(dx) + abs(dy) <= 2})
    idx = {c: i for i, c in enumerate(U)}
    PM = sum(1 << idx[c] for c in P)
    popcount = int.bit_count

    def cells_of(mask):
        out, i = [], 0
        while mask:
            if mask & 1: out.append(U[i])
            mask >>= 1; i += 1
        return out

    def h(st):
        c, _, _, _, ox, oy = st
        return popcount(PM & ~c) + popcount(c & ~PM) + (ox < 0) + (oy < 0)

    def nxt(st, op):
        c, latch, pushed, pin, ox, oy = st
        kind, d = op
        if kind == 'push':   return (c, d, True, pin, ox, oy)
        if kind == 'pin':    return (c, latch, pushed, c, ox, oy)
        if kind == 'mirror': return (c, latch, pushed, pin, ox, -oy) if d == 'R' else (c, latch, pushed, pin, -ox, oy)
        cells = [(ox * x, oy * y) for x, y in cells_of(c)]          # actual frame
        scope = cells if pin is None else [(ox * x, oy * y) for x, y in cells_of(c & pin)]
        if not scope: return None
        lines = [line_of(latch, q) for q in scope]
        if pushed:
            count = {}
            for k in lines: count[k] = count.get(k, 0) + 1
            k = max(count, key=lambda k: (count[k], k))
        else:
            k = max(lines)
        line = k if latch == d else reach(latch, scope, k)
        a = reach(d, cells, line)
        ax, ay = cell_at(d, line, a + 1 if kind == 'add' else a)
        q = (ox * ax, oy * ay)                                        # back to P's frame
        if q not in idx: return None
        c2 = c | (1 << idx[q]) if kind == 'add' else c & ~(1 << idx[q])
        if popcount(c2 & ~PM) > allowed_extra: return None
        return (c2, latch, False, pin, ox, oy)

    parent, best = {}, {}
    heap, tie = [], 0
    for d, seg in runs(Pset):
        st = (sum(1 << idx[q] for q in seg), d, False, None, 1, 1)
        if st not in best:
            best[st] = 0; parent[st] = (None, (d, len(seg)))
            heapq.heappush(heap, (weight * h(st), tie, st)); tie += 1
    while heap:
        f, _, st = heapq.heappop(heap)
        g = best[st]
        if st[0] == PM and st[4] == 1 and st[5] == 1:
            ops = []
            while parent[st][0] is not None:
                prev, op = parent[st]; ops.append(op); st = prev
            d, j = parent[st][1]
            return d, j, ops[::-1]
        if len(best) > max_states: return None
        for op in OPS:
            if op[0] == 'sub' and not allow_sub: continue
            nx = nxt(st, op)
            if nx is None: continue
            if nx not in best or g + 1 < best[nx]:
                best[nx] = g + 1; parent[nx] = (st, op)
                heapq.heappush(heap, (g + 1 + weight * h(nx), tie, nx)); tie += 1
    return None
