import re, sys, itertools, os
# The blog posts' source; by default a clone of the blog repo next to this one.
BLOG=os.path.join(os.environ.get("SHAPE_BLOG") or os.path.join(os.path.dirname(os.path.abspath(__file__)),
    "..", "..", "pUrGe12.github.io", "content", "blog"), "")

def cells_of(html):
    return frozenset((int(c), -int(r)) for r,c in re.findall(r'grid-area:(\d+)/(\d+)', html))

def norm(s):
    if not s: return frozenset()
    mx=min(x for x,y in s); my=min(y for x,y in s)
    return frozenset((x-mx,y-my) for x,y in s)

def show(s):
    s=norm(s); W=max(x for x,_ in s)+1; H=max(y for _,y in s)+1
    return "\n".join("".join("#" if (x,y) in s else "." for x in range(W)) for y in reversed(range(H)))

def tokens(tex):
    t=tex.replace(r'\left','').replace(r'\right','').replace(' ','')
    t=t.replace('{','').replace('}','').replace('(', '(').replace('^M_','^M_')
    out=[]; i=0
    while i<len(t):
        m=re.match(r'A_([RC])\^\(?(\d+)\)?',t[i:])
        if m: out.append(('A',m.group(1),int(m.group(2)))); i+=m.end(); continue
        m=re.match(r'([+-])1_([RC])',t[i:])
        if m: out.append((m.group(1),m.group(2))); i+=m.end(); continue
        m=re.match(r'\^M_([RC])',t[i:])
        if m: out.append(('M',m.group(1))); i+=m.end(); continue
        m=re.match(r'\^M',t[i:])
        if m: out.append(('M',None)); i+=m.end(); continue
        m=re.match(r'_([RCP])',t[i:])
        if m: out.append(('_',m.group(1))); i+=m.end(); continue
        if t[i] in '()': i+=1; continue
        raise ValueError(t[i:])
    return out

class Opts:
    bareM='R'        # bare ^M means M_R, or 'latch' = use current latch type
    refScope=True    # intermediate reference cell (rho's rightmost / gamma's topmost) taken within pin scope
def run(toks, o=Opts, trace=False):
    cells=set(); typ=None; pushed=False; pin=None
    for tk in toks:
        if tk[0]=='A':
            _,X,j=tk; typ=X
            cells={(i,0) for i in range(j)} if X=='R' else {(0,i) for i in range(j)}
        elif tk[0]=='_' and tk[1]=='P':
            pin=set(cells)
        elif tk[0]=='_':
            typ=tk[1]; pushed=True
        elif tk[0]=='M':
            ax=tk[1] or (typ if o.bareM=='latch' else o.bareM)
            f=(lambda p:(p[0],-p[1])) if ax=='R' else (lambda p:(-p[0],p[1]))
            cells={f(p) for p in cells}
            if pin is not None: pin={f(p) for p in pin}
        else:
            sign,U=tk
            S=cells if pin is None else (pin & cells)
            if typ=='R':
                rows={}
                for x,y in S: rows[y]=rows.get(y,0)+1
                rho = max(rows, key=lambda y:(rows[y],y)) if pushed else max(rows)
                ref=(S if o.refScope else cells)
                if U=='R':
                    tx=max(x for x,y in cells if y==rho); tgt=(tx+1,rho); ext=(tx,rho)
                else:
                    col=max(x for x,y in ref if y==rho)
                    ty=max(y for x,y in cells if x==col); tgt=(col,ty+1); ext=(col,ty)
            else:
                cols={}
                for x,y in S: cols[x]=cols.get(x,0)+1
                gam = max(cols, key=lambda x:(cols[x],x)) if pushed else max(cols)
                ref=(S if o.refScope else cells)
                if U=='C':
                    ty=max(y for x,y in cells if x==gam); tgt=(gam,ty+1); ext=(gam,ty)
                else:
                    row=max(y for x,y in ref if x==gam)
                    tx=max(x for x,y in cells if y==row); tgt=(tx+1,row); ext=(tx,row)
            if sign=='+': cells.add(tgt)
            else: cells.discard(ext)
            pushed=False
        if trace: print(tk); print(show(cells)); print()
    return norm(cells), typ, pushed
