import sys, random, time
from collections import deque

# ---------------------------------------------------------------- packing
# bit 0        latch (0=R, 1=C)
# bit 1        pinned?  0 = scope is the whole shape and tracks it as it grows
# bits 2..6    W          bits 7..11   H
# bits 12..31  pin summary, rows  (4 x 5 bits)   only meaningful when pinned
# bits 32..51  pin summary, cols  (4 x 5 bits)   only meaningful when pinned
# bits 52..    cell mask, bit (r-1)*W + (c-1)
#
# When not pinned the two summaries are forced to zero so that states which
# differ only in stale summary bits collapse together.

ZERO = (0, 0, 0, 0)

def pack(W, H, mask, prS, pcS, lt, pinned):
    if not pinned: prS = pcS = ZERO
    v = (1 if lt == 'C' else 0) | (2 if pinned else 0) | (W << 2) | (H << 7)
    for i, x in enumerate(prS): v |= x << (12 + 5 * i)
    for i, x in enumerate(pcS): v |= x << (32 + 5 * i)
    return v | (mask << 52)

def unpack(v):
    return ((v >> 2) & 31, (v >> 7) & 31, v >> 52,
            tuple((v >> (12 + 5 * i)) & 31 for i in range(4)),
            tuple((v >> (32 + 5 * i)) & 31 for i in range(4)),
            'C' if v & 1 else 'R', bool(v & 2))

def scope(W, H, mask, prS, pcS, pinned):
    """The summaries selection should actually read."""
    return (prS, pcS) if pinned else profile(W, H, mask)

# ---------------------------------------------------------------- geometry
def row_bits(mask, W, r):   return (mask >> ((r - 1) * W)) & ((1 << W) - 1)
def maxcol(mask, W, r):     return row_bits(mask, W, r).bit_length()
def minrow(mask, W, H, c):
    bit = 1 << (c - 1)
    for r in range(1, H + 1):
        if (mask >> ((r - 1) * W)) & bit: return r
    return 0

def cells_of(W, H, mask):
    return [((i % W) + 1, (i // W) + 1) for i in range(W * H) if mask >> i & 1]

def mask_of(cells, W):
    m = 0
    for c, r in cells: m |= 1 << ((r - 1) * W + (c - 1))
    return m

def summ(counts):
    m = max(counts); first = last = fnz = lnz = 0
    for i, v in enumerate(counts, 1):
        if v == m:
            if not first: first = i
            last = i
        if v:
            if not fnz: fnz = i
            lnz = i
    return (first, last, fnz, lnz)

def profile(W, H, mask):
    pr = [0] * H; pc = [0] * W
    for c, r in cells_of(W, H, mask): pr[r - 1] += 1; pc[c - 1] += 1
    return summ(pr), summ(pc)

# ---------------------------------------------------------------- operations
def do_add(W, H, mask, prS, pcS, latch, mode, unit, pinned):
    """Return the new packed state, or None if the cell is already occupied."""
    sprS, spcS = scope(W, H, mask, prS, pcS, pinned)
    prS, pcS = sprS, spcS
    if latch == 'R':
        rho = prS[0] if mode == 'most' else prS[2]
        if unit == 'R': c, r = maxcol(mask, W, rho) + 1, rho
        else:
            c = maxcol(mask, W, rho); r = minrow(mask, W, H, c) - 1
    else:
        gam = pcS[1] if mode == 'most' else pcS[3]
        if unit == 'C': c, r = gam, minrow(mask, W, H, gam) - 1
        else:
            rs = minrow(mask, W, H, gam); c, r = maxcol(mask, W, rs) + 1, rs
    if 1 <= c <= W and 1 <= r <= H and mask >> ((r - 1) * W + (c - 1)) & 1:
        return None
    dr = 1 if r == 0 else 0           # growing upward shifts every row down
    nW = max(W, c); nH = H + dr
    old = cells_of(W, H, mask)
    nm = mask_of([(cc, rr + dr) for cc, rr in old] + [(c, r + dr)], nW)
    return pack(nW, nH, nm,
                tuple(x + dr for x in sprS), spcS, latch, pinned)

def rev(t, L): return (L + 1 - t[1], L + 1 - t[0], L + 1 - t[3], L + 1 - t[2])

def do_mirror(W, H, mask, prS, pcS, lt, pinned, axis):
    cs = cells_of(W, H, mask)
    if axis == 'C':
        return pack(W, H, mask_of([(W + 1 - c, r) for c, r in cs], W),
                    prS, rev(pcS, W), lt, pinned)
    return pack(W, H, mask_of([(c, H + 1 - r) for c, r in cs], W),
                rev(prS, H), pcS, lt, pinned)

def do_pin(W, H, mask, lt):
    a, b = profile(W, H, mask)
    return pack(W, H, mask, a, b, lt, True)

def successors(v, use_p):
    W, H, mask, prS, pcS, lt, pinned = unpack(v)
    out = [do_mirror(W, H, mask, prS, pcS, lt, pinned, 'C'),
           do_mirror(W, H, mask, prS, pcS, lt, pinned, 'R')]
    if use_p: out.append(do_pin(W, H, mask, lt))
    return out

def additions(v):
    W, H, mask, prS, pcS, lt, pinned = unpack(v)
    out = []
    for X in 'RC':
        for u in 'RC':
            s = do_add(W, H, mask, prS, pcS, X, 'most', u, pinned)
            if s is not None: out.append(s)
    for u in 'RC':
        s = do_add(W, H, mask, prS, pcS, lt, 'default', u, pinned)
        if s is not None: out.append(s)
    return out

def seeds(n):
    out = []
    for horiz in (True, False):
        W, H = (n, 1) if horiz else (1, n)
        mask = (1 << n) - 1 if horiz else sum(1 << (r * W) for r in range(n))
        out.append(pack(W, H, mask, ZERO, ZERO, 'R' if horiz else 'C', False))
    return out

def shape_key(v):
    W, H, mask, _, _, _, _ = unpack(v)
    return (W, H, mask)

# ---------------------------------------------------------------- enumeration
def norm(cells):
    mc = min(c for c, r in cells); mr = min(r for c, r in cells)
    return frozenset((c - mc + 1, r - mr + 1) for c, r in cells)

def all_polyominoes(n):
    cur = {frozenset({(1, 1)})}
    for _ in range(n - 1):
        nxt = set()
        for s in cur:
            for c, r in s:
                for dc, dr in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                    p = (c + dc, r + dr)
                    if p not in s: nxt.add(norm(set(s) | {p}))
        cur = nxt
    return cur

def to_key(s):
    W = max(c for c, r in s); H = max(r for c, r in s)
    return (W, H, mask_of(s, W))

def render(s):
    W = max(c for c, r in s); H = max(r for c, r in s)
    return "\n".join("".join('X' if (c, r) in s else '.'
                             for c in range(1, W + 1)) for r in range(1, H + 1))

# ---------------------------------------------------------------- sweep
def sweep(N, use_p=True, max_states=None):
    cur = set(seeds(1)); reached = {}
    t0 = time.time()
    for n in range(1, N + 1):
        cur |= set(seeds(n))
        q = deque(cur)
        while q:
            for nx in successors(q.popleft(), use_p):
                if nx not in cur: cur.add(nx); q.append(nx)
        reached[n] = {shape_key(v) for v in cur}
        print(f"  n={n:>2}: {len(reached[n]):>9} shapes, {len(cur):>10} states, "
              f"{time.time()-t0:>6.0f}s", flush=True)
        if max_states and len(cur) > max_states:
            print(f"  stopping: state count passed --max-states"); break
        if n == N: break
        nxt = set()
        for v in cur: nxt.update(additions(v))
        cur = nxt
    return reached

# ---------------------------------------------------------------- targeted
def orbit(s):
    o = {norm(s)}
    for _ in range(2):
        W = lambda x: max(c for c, r in x); H = lambda x: max(r for c, r in x)
        o |= {norm({(W(x) + 1 - c, r) for c, r in x}) for x in o}
        o |= {norm({(c, H(x) + 1 - r) for c, r in x}) for x in o}
    return o

def connected(s):
    s = set(s); st = [next(iter(s))]; seen = {st[0]}
    while st:
        c, r = st.pop()
        for dc, dr in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            p = (c + dc, r + dr)
            if p in s and p not in seen: seen.add(p); st.append(p)
    return len(seen) == len(s)

def sub_keys(target):
    """Normalised keys of every connected sub-shape of the target, closed
    under mirrors.  Grown incrementally rather than scanning all 2^n subsets,
    which is what makes this usable past n=12."""
    T = set(norm(target))
    seen = {frozenset({c}) for c in T}
    cur = set(seen)
    while cur:
        nxt = set()
        for sub in cur:
            for c, r in sub:
                for dc, dr in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                    p = (c + dc, r + dr)
                    if p in T and p not in sub:
                        t = frozenset(sub | {p})
                        if t not in seen: seen.add(t); nxt.add(t)
        cur = nxt
    keys = set()
    for sub in seen:
        for m in orbit(sub): keys.add(to_key(m))
    return keys

def is_reachable(target, use_p=True):
    """Prune the search to sub-shapes of the target's mirror orbit.
    Cheap at any n - this is the mode that scales."""
    allowed = sub_keys(target)
    tk = to_key(norm(target)); N = len(target)
    frontier = [v for v in
                (s for j in range(1, N + 1) for s in seeds(j))
                if shape_key(v) in allowed]
    seen = set(frontier); q = deque(frontier)
    while q:
        v = q.popleft()
        if shape_key(v) == tk: return True
        for nx in successors(v, use_p):
            if nx not in seen and shape_key(nx) in allowed:
                seen.add(nx); q.append(nx)
        W, H, mask, _, _, _, _ = unpack(v)
        if bin(mask).count('1') >= N: continue
        for nx in additions(v):
            if nx not in seen and shape_key(nx) in allowed:
                seen.add(nx); q.append(nx)
    return False

def random_polyomino(n, rng):
    s = {(0, 0)}
    while len(s) < n:
        cand = [(c + dc, r + dr) for c, r in s
                for dc, dr in ((1, 0), (-1, 0), (0, 1), (0, -1))
                if (c + dc, r + dr) not in s]
        s.add(rng.choice(cand))
    return norm(s)

def parse_shapes(path):
    out = []; block = []
    for line in open(path):
        line = line.rstrip("\n")
        if not line.strip():
            if block: out.append(block); block = []
        else: block.append(line)
    if block: out.append(block)
    return [norm({(c + 1, r + 1) for r, row in enumerate(b)
                  for c, ch in enumerate(row) if ch not in '. '}) for b in out]

# ---------------------------------------------------------------- main
def main():
    if len(sys.argv) < 2: print(__doc__); return
    cmd = sys.argv[1]
    use_p = '--nop' not in sys.argv
    tag = "with P" if use_p else "P DISABLED"

    if cmd == 'sweep':
        N = int(sys.argv[2])
        ms = None
        for a in sys.argv:
            if a.startswith('--max-states='): ms = int(a.split('=')[1])
        if N >= 12:
            print(f"warning: n={N} will likely exhaust memory. See the "
                  f"feasibility notes; consider `sample` instead.\n")
        print(f"BFS ({tag}):")
        reached = sweep(N, use_p, ms)
        print(f"\n{'n':>3} {'reachable':>10} {'total':>10} {'missing':>8}")
        for n in sorted(reached):
            allp = {to_key(s) for s in all_polyominoes(n)}
            miss = allp - reached[n]
            print(f"{n:>3} {len(reached[n]):>10} {len(allp):>10} {len(miss):>8}")
            for k in sorted(miss)[:6]:
                W, H, mask = k
                print(render(set(cells_of(W, H, mask))) + "\n")

    elif cmd == 'check':
        for s in parse_shapes(sys.argv[2]):
            ok = is_reachable(s, use_p)
            print(f"n={len(s)}  reachable={ok}  ({tag})")
            print(render(s) + "\n")

    elif cmd == 'sample':
        n = int(sys.argv[2]); k = int(sys.argv[3])
        rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 0)
        print(f"sampling {k} random {n}-cell polyominoes ({tag})")
        print("note: random growth is NOT uniform over polyominoes - it is\n"
              "biased toward compact shapes, and the known failures are\n"
              "sparse/ring-like, so this UNDERSTATES the missing fraction.\n")
        bad = []; t0 = time.time()
        for i in range(1, k + 1):
            s = random_polyomino(n, rng)
            if not is_reachable(s, use_p): bad.append(s)
            if i % 10 == 0:
                print(f"  {i}/{k}  unreachable so far: {len(bad)}  "
                      f"{time.time()-t0:.0f}s", flush=True)
        print(f"\n{len(bad)}/{k} unreachable")
        for s in bad[:10]: print(render(s) + "\n")

    else: print(__doc__)

if __name__ == '__main__':
    main()