exec(open('sector.py').read().split("if __name__")[0])
import time; T=time.time()
extra=[i for i in range(240) if i not in Dint]
S5=set()
for r in extra:
    S=closure(Dint+[r]); 
    if rank(S)==5: S5.add(S)
print('rank-5 sectors containing internal D4:',collections.Counter(len(s) for s in S5),f'{time.time()-T:.0f}s',flush=True)
S6=set()
for S in S5:
    for r in extra:
        if r in S: continue
        X=closure(list(S)+[r])
        if rank(X)==6: S6.add(X)
print('rank-6 sectors containing internal D4 (size: count):',dict(collections.Counter(len(s) for s in S6)),f'{time.time()-T:.0f}s',flush=True)
import pickle; pickle.dump((S5,S6),open('sectors.pkl','wb'))
