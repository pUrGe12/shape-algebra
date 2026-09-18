# For every fixed polyomino up to N: does it have a cell that could have been ADDED LAST?
# An addition always puts the new cell right next to the far cell of a row/column
# (mirrors give all 4 sides), and additions never disconnect. So the last added cell c must:
#   - have a neighbour d in the same row/column, with nothing beyond c on that line, and
#   - leave P - c connected.
# If no cell qualifies, the shape cannot be built with additions only (whatever the selection).
import sys, time
from sim import show
N=int(sys.argv[1])
DIRS=((1,0),(-1,0),(0,1),(0,-1))
def connected_without(P,c):
    rest=P-{c}; start=next(iter(rest)); seen={start}; st=[start]
    while st:
        x,y=st.pop()
        for dx,dy in DIRS:
            n=(x+dx,y+dy)
            if n in rest and n not in seen: seen.add(n); st.append(n)
    return len(seen)==len(rest)
def peelable(P):
    if len(P)==1: return True
    rmax={};rmin={};cmax={};cmin={}
    for x,y in P:
        rmax[y]=max(rmax.get(y,x),x); rmin[y]=min(rmin.get(y,x),x)
        cmax[x]=max(cmax.get(x,y),y); cmin[x]=min(cmin.get(x,y),y)
    for (x,y) in P:
        deg=sum((x+dx,y+dy) in P for dx,dy in DIRS)
        for dx,dy in DIRS:
            if (x-dx,y-dy) not in P: continue
            ext = (dx==1 and x==rmax[y]) or (dx==-1 and x==rmin[y]) or (dy==1 and y==cmax[x]) or (dy==-1 and y==cmin[x])
            if ext and (deg==1 or connected_without(P,(x,y))): return True
    return False
counts=[0]*(N+1); bad=[0]*(N+1); examples={}; blocked=[]
poly=set()
def ok(c): return c[1]>0 or (c[1]==0 and c[0]>=0)
def rec(untried, seen):          # Redelmeier: each fixed polyomino exactly once
    untried=list(untried)
    while untried:
        c=untried.pop(); poly.add(c); n=len(poly); counts[n]+=1
        if not peelable(poly):
            bad[n]+=1; blocked.append(sorted(poly))
            examples.setdefault(n,[]).append(frozenset(poly)) if len(examples.get(n,[]))<6 else None
        if n<N:
            new=[]
            for dx,dy in DIRS:
                nb=(c[0]+dx,c[1]+dy)
                if ok(nb) and nb not in seen: new.append(nb)
            seen.update(new); rec(untried+new, seen); seen.difference_update(new)
        poly.discard(c)
t=time.time(); rec([(0,0)],{(0,0)})
for n in range(1,N+1): print(f"N={n:2}  fixed polyominoes={counts[n]:>9}  no cell can be added last={bad[n]:>6}")
for n in sorted(examples):
    print(f"\nexamples at N={n}:")
    for s in examples[n][:4]: print(show(s)); print()
import json; json.dump(blocked, open(f"blocked_upto_{N}.json","w"))
print(f"{time.time()-t:.0f}s")
