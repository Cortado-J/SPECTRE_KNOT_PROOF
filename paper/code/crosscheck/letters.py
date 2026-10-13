import os, json
C=json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','hierarchy','')+'combin_8.json'))
E=json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'fig51_encoding.json')))['fig42']
N=['Gamma','Delta','Theta','Lambda','Xi','Pi','Sigma','Phi','Psi']
lab={s:[E[s][(3+j)%6] for j in range(6)] for s in N}
for m in sorted(C['LEN'],key=int):
    by={}
    for s in N:
        for j,l in enumerate(C['LEN'][m][s]): by.setdefault(lab[s][j][0],set()).add(l)
    print(m,{k:sorted(v) for k,v in sorted(by.items())})
# M respects letter classes? M row (T,J) -> counts over (s,j)
M=json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','hierarchy','')+'M.json'))
print(type(M), list(M.keys())[:5] if isinstance(M,dict) else len(M))
ST=C['ST']['1']
rows={}
for T in N:
    for J,seq in enumerate(ST[T]['pside']):
        cnt={}
        for t in seq:
            c,j=map(int,t.split('.')); s=ST[T]['kids'][c]; x=lab[s][j][0]; cnt[x]=cnt.get(x,0)+1
        rows.setdefault(lab[T][J][0],set()).add(tuple(sorted(cnt.items())))
for k,v in sorted(rows.items()): print(k,v)
