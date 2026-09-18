# Every fixed polyomino with up to N cells, each exactly once (Redelmeier's method).
DIRS = ((1, 0), (-1, 0), (0, 1), (0, -1))

def fixed_polyominoes(N):
    poly = []
    def ok(c): return c[1] > 0 or (c[1] == 0 and c[0] >= 0)
    def rec(untried, seen):
        untried = list(untried)
        while untried:
            c = untried.pop(); poly.append(c)
            yield list(poly)
            if len(poly) < N:
                new = [(c[0] + dx, c[1] + dy) for dx, dy in DIRS]
                new = [nb for nb in new if ok(nb) and nb not in seen]
                seen.update(new)
                yield from rec(untried + new, seen)
                seen.difference_update(new)
            poly.pop()
    yield from rec([(0, 0)], {(0, 0)})

def normalize(cells):
    mx = min(x for x, _ in cells); my = min(y for _, y in cells)
    return sorted((x - mx, y - my) for x, y in cells)
