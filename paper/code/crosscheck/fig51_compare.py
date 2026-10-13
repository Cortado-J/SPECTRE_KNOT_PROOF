import os, json, itertools, sys
# usage: python3 fig51_compare.py [directory with fig51_encoding.json and gamma_centres.json]  (default: this folder)
ENC_DIR = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
E=json.load(open(os.path.join(ENC_DIR,'fig51_encoding.json')))
G=json.load(open(os.path.join(ENC_DIR,'gamma_centres.json')))
CODE=json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','hierarchy','')+'combin_8.json'))
NAMES=['Gamma','Delta','Theta','Lambda','Xi','Pi','Sigma','Phi','Psi']
DOTS={'Gamma':[(440,92),(747,152),(236,329),(133,506),(747,624),(236,683)],
'Delta':[(557,94),(659,272),(148,331),(46,626),(659,626),(455,862)],
'Theta':[(586,90),(688,268),(176,327),(74,504),(381,799),(586,799)],
'Lambda':[(585,96),(688,273),(176,332),(74,510),(688,628),(483,864)],
'Xi':[(361,45),(668,222),(157,281),(54,458),(361,754),(566,754)],
'Pi':[(366,73),(673,250),(162,310),(60,487),(673,605),(469,841)],
'Sigma':[(579,57),(272,116),(681,234),(68,588),(681,588),(477,825)],
'Phi':[(561,71),(663,248),(152,307),(49,484),(663,602),(356,780)],
'Psi':[(385,71),(691,248),(180,307),(78,484),(691,602),(385,780)]}
SX,SY=102.5,59.1
WSC=3308/1414
NB=[(2,0),(1,-3),(-1,-3),(-2,0),(-1,3),(1,3)]
VA={-30:(1,1),30:(1,-1),90:(0,-2),150:(-1,-1),210:(-1,1),270:(0,2)}
def evs(c,d):
    a=VA[60*d-30]; b=VA[(60*d+30) if 60*d+30<=270 else 60*d+30-360]
    return (c[0]+a[0],c[1]+a[1]),(c[0]+b[0],c[1]+b[1])
def match(x,y):
    if x=='h' or y=='h': return x==y
    return x[0]==y[0] and {x[1],y[1]}=={'+','-'}
L42=E['fig42']; problems=[]; out=[]
KAPPA={}  # kind -> set of kappa
SIGMA=None
for T in NAMES:
    F=E['fig51'][T]; posn=list(F.keys()); P={p:tuple(E['pos'][p]) for p in posn}
    at={P[p]:p for p in posn}
    nbr=lambda p,d:(at.get((P[p][0]+NB[d][0],P[p][1]+NB[d][1])))
    # 1. paper-internal: rotations r such that labels at page dir d = L42[kind][(d-r)%6] match across shared edges
    sols=[]
    for rs in itertools.product(range(6),repeat=len(posn)):
        R=dict(zip(posn,rs)); ok=True
        for p in posn:
            for d in range(3):
                q=nbr(p,d)
                if q and not match(L42[F[p]][(d-R[p])%6],L42[F[q]][(d+3-R[q])%6]): ok=False;break
            if not ok: break
        if ok: sols.append(R)
    if len(sols)!=1: problems.append(f'{T}: {len(sols)} rotation solutions'); 
    R=sols[0] if sols else None
    if R is None: continue   # the labels admit no consistent rotation: already reported
    # 2. code child -> position
    S=CODE['ST']['1'][T]; kids=S['kids']; sides=[[None if s=='R' else tuple(map(int,s.split('.'))) for s in ss] for ss in S['sides']]
    cadj={c:sorted(x[0] for x in sides[c] if x) for c in range(len(kids))}
    maps=[]
    for perm in itertools.permutations(posn):
        if any(F[perm[c]]!=kids[c] for c in range(len(kids))): continue
        m=dict(enumerate(perm)); inv={v:k for k,v in m.items()}
        if all(sorted(inv[q] for d in range(6) if (q:=nbr(m[c],d)))==cadj[c] for c in m): maps.append(m)
    if len(maps)!=1: problems.append(f'{T}: {len(maps)} child-position maps')
    m=maps[0]; inv={v:k for k,v in m.items()}
    # 3. per-child offset k_c with global orientation sigma
    best=None
    for sg in (1,-1):
        K={}
        for c in m:
            ks=[k for k in range(6) if all((inv.get(nbr(m[c],(k+sg*j)%6)) if nbr(m[c],(k+sg*j)%6) else None)==(sides[c][j][0] if sides[c][j] else None) for j in range(6))]
            # also partner side index
            ks=[k for k in ks]
            K[c]=ks
        if all(len(v)>=1 for v in K.values()): best=(sg,K)
    sg,K=best
    if SIGMA is None: SIGMA=sg
    elif SIGMA!=sg: problems.append(f'{T}: orientation differs')
    amb=[c for c in K if len(K[c])!=1]
    Kc={c:K[c][0] for c in K if len(K[c])==1}
    # partner-side check (resolves ambiguity: child with single neighbour has rotation fixed by partner j')
    for c in m:
        for j in range(6):
            if sides[c][j]:
                c2,j2=sides[c][j]
                if c in Kc and c2 in Kc:
                    d=(Kc[c]+sg*j)%6; d2=(Kc[c2]+sg*j2)%6
                    if d2!=(d+3)%6: problems.append(f'{T}: partner side mismatch {c}.{j}-{c2}.{j2}')
    # 4. kappa per kind: fig42 edge index of code side 0 = k_c - r_c
    for c in Kc:
        KAPPA.setdefault(kids[c],[]).append(((Kc[c]-R[m[c]])%6,T,m[c]))
    # 5. parent rim from figure
    cen={p:(P[p][0],P[p][1]) for p in posn}
    rim=[]
    for p in posn:
        for d in range(6):
            if not nbr(p,d): a,b=evs(cen[p],d); rim.append((a,b,p,d))
    nxt={r[0]:r for r in rim}; assert len(nxt)==len(rim)
    gx,gy=G[T]; dots=set()
    for (px,py) in DOTS[T]:
        X=2+(px-gx)/SX; Y=3+(py-gy)/SY
        if abs(X-round(X))>0.15 or abs(Y-round(Y))>0.25: problems.append(f'{T}: dot off-lattice {X:.2f},{Y:.2f}')
        dots.add((round(X),round(Y)))
    if not dots<=set(nxt): problems.append(f'{T}: dot not on rim {dots-set(nxt)}')
    # walk from a dot
    start=sorted(dots)[0]; cyc=[]; v=start
    while True:
        r=nxt[v]; cyc.append(r); v=r[1]
        if v==start: break
    if len(cyc)!=len(rim): problems.append(f'{T}: rim not single cycle')
    # split into fig sides (ccw on page)
    figsides=[]; cur=[]
    for r in cyc:
        if r[0] in dots and cur: figsides.append(cur); cur=[]
        cur.append(r)
    figsides.append(cur)
    # convert to code tags (c, j): j = sg*(d - k_c)
    def tag(r):
        c=inv[r[2]]; j=(sg*(r[3]-Kc[c]))%6; return f'{c}.{j}'
    figtags=[[tag(r) for r in s] for s in figsides]
    # code pside, parent orientation: code parent ccw (own frame) -> page orientation is -sg? try both
    code=S['pside']; found=None
    for po in (1,-1):
        seqs=[s if po==1 else list(reversed(s)) for s in code]
        if po==-1: seqs=list(reversed(seqs))
        for sh in range(6):
            if [seqs[(sh+i)%6] for i in range(6)]==figtags: found=(po,sh)
    if not found: problems.append(f'{T}: parent sides mismatch\n  fig ={figtags}\n  code={code}')
    # 6. labels on parent sides
    box=E['crop_boxes_display'][T]
    lab_of_side={}
    for (lb,dx,dy) in E['labels_display'][T]:
        px=(dx-box[0])*WSC; py=(dy-box[1])*WSC
        best=None
        for i,s in enumerate(figsides):
            for r in s:
                mx=(r[0][0]+r[1][0])/2; my=(r[0][1]+r[1][1])/2
                qx=gx+(mx-2)*SX; qy=gy+(my-3)*SY
                dd=(qx-px)**2+(qy-py)**2
                if best is None or dd<best[0]: best=(dd,i)
        if best[1] in lab_of_side: problems.append(f'{T}: two labels on one fig side')
        lab_of_side[best[1]]=lb
    # paper-internal: parent labels are the reflection of fig42[T]
    cycp=[lab_of_side.get(i) for i in range(6)]
    ref=list(reversed(L42[T])); okp=any([ref[(s+i)%6] for i in range(6)]==cycp for s in range(6))
    if not okp: problems.append(f'{T}: parent labels {cycp} not a reflection of fig42 {L42[T]}')
    out.append(dict(T=T,map={c:m[c] for c in m},rot=R,k=K,amb=amb,sg=sg,parent=found,figlabels=cycp))
    # store parent side J -> label
    if found:
        po,sh=found
        # fig side i corresponds to code side index: seqs index (sh+i)%6 ; if po==-1 seqs reversed
        for i in range(6):
            si=(sh+i)%6; J=si if po==1 else 5-si
            out[-1].setdefault('Jlab',{})[J]=cycp[i]
for o in out: print(o['T'],'map',o['map'],'sigma',o['sg'],'parent(orient,shift)',o['parent'],'amb',o['amb']); print('   rot',o['rot']); print('   parent side J->label',o.get('Jlab'))
print('sigma(global)',SIGMA)
print('kappa per kind (fig42 edge of code side 0; must be constant):')
KK={}
for s,v in KAPPA.items():
    vals=set(x[0] for x in v); print(' ',s,sorted(vals),len(v),'placements'); KK[s]=vals
    if len(vals)!=1: problems.append(f'kappa not constant for {s}: {v}')
# parent label check: label of code parent side J of kind T == fig42[T][kappa_T + sigma*J]
for o in out:
    T=o['T']
    if len(KK.get(T,()))!=1 or 'Jlab' not in o: continue
    kap=next(iter(KK[T]))
    for J,lb in o['Jlab'].items():
        want=L42[T][(kap+SIGMA*J)%6]
        if want!=lb: problems.append(f'{T}: parent side {J} labelled {lb} in Fig 5.1, code indexing predicts {want}')
print('code side j of kind s -> Fig 4.2 label:')
for s in NAMES:
    if len(KK.get(s,()))==1: kap=next(iter(KK[s])); print(' ',s,[L42[s][(kap+SIGMA*j)%6] for j in range(6)])
print('PROBLEMS:' if problems else 'NO PROBLEMS'); [print(' ',p) for p in problems]
