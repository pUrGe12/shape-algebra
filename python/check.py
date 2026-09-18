# Cross-check a search result with the original simulator (sim.py).
from sim import run, norm, Opts
Opts.bareM = 'R'; Opts.refScope = True
def to_sim(d, j, ops):
    t = [('A', d, j)]
    for k, x in ops:
        t.append({'add': ('+', x), 'sub': ('-', x), 'mirror': ('M', x), 'push': ('_', x), 'pin': ('_', 'P')}[k])
    return t
def builds(formula, P):
    d, j, ops = formula
    return run(to_sim(d, j, ops))[0] == norm(frozenset(map(tuple, P)))
