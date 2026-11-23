exec(open('tick.py').read().split("for k in (2,5,8):")[0].replace("print(","(lambda *a,**k:None)("))
S=L[5]
ext=sorted({min(a,int(neg[a])) for a in S if a not in Dint})
PASSES.clear(); r=test(S,True,True,extra_orth=[t])
c=collections.Counter()
for a,b,w,K1,K2 in PASSES:
    gen=[k for k in range(3) if k not in (K1,K2)][0]
    wrole='extra root %d'%ext.index(min(w,int(neg[w]))) if min(w,int(neg[w])) in ext else 'internal D4'
    c[(KEYS[gen],'doublets in',KEYS[K1],'singlets in',KEYS[K2],'weak =',wrole)]+=1
for k,v in sorted(c.items()): print(v,k)
by=collections.defaultdict(set)
for a,b,w,K1,K2 in PASSES:
    gen=[k for k in range(3) if k not in (K1,K2)][0]; by[(a,b,w)].add((gen,K1))
cov=collections.Counter(tuple(sorted({g for g,_ in v})) for v in by.values())
print('colour/weak choices by generations they can host:',dict(cov))
