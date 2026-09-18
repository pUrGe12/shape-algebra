import re, itertools
from sim import *
c1=open(BLOG+"confluence.md").read(); c2=open(BLOG+"shape_algebra_2.md").read()
cases=[]
for pic,eq in re.findall(r'<div class="tetro-pic">(.*?)</div><div class="tetro-eq">\$(.*?)\$</div>', c1):
    cases.append(("tetro "+eq, eq, norm(cells_of(pic))))
# display formulas followed by a sequence row: compare to last picture in the next polyeq row
for src,name in ((c1,"p1"),(c2,"p2")):
    for m in re.finditer(r'\$\$\n(.*?)\n\$\$', src, re.S):
        tex=m.group(1).strip()
        if 'A_' not in tex or '=' in tex or 'implies' in tex or r'\to' in tex or 'geq' in tex: continue
        row=re.search(r'<div class="polyeq">(.*?)</div>', src[m.end():]).group(1)
        polys=re.findall(r'<span class="poly">(.*?)</span>', row)
        cases.append((name+" "+tex[:50], tex, norm(cells_of(polys[-1]))))
for bareM,ref in itertools.product(['R','C','latch'],[True,False]):
    Opts.bareM=bareM; Opts.refScope=ref
    fails=[n for n,tex,want in cases if run(tokens(tex))[0]!=want]
    print(f"bareM={bareM:5} refScope={ref!s:5}: {len(cases)-len(fails)}/{len(cases)} match", fails)
