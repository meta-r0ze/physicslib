"""Writes sector_data.json: the derived sector, colour/weak roots, time vector, integer charge direction, and one representative placement per generation (run after place.py)."""
import pickle, numpy as np, json
from fractions import Fraction
exec(open('base.py').read())
a,b,w,y,CH,WL=pickle.load(open('placement.pkl','rb'))
S5,S6=pickle.load(open('sectors.pkl','rb'))
L=sorted([s for s in S6 if len(s)==28],key=sorted); S=L[5]
cvec=cu-2*cv
fwd=[i for i in range(240) if all(P[i,j]==0 for j in Dint) and (int(RA[i]@G@cvec)%43)==1]
t=next(RA[i]+RA[j] for i in fwd for j in fwd if i!=j and P[i,j]==0)
ext=sorted({min(x,idx[tuple(-RA[x])]) for x in S if x not in Dint})
# integer charge direction: scale y so pairings 3Y are integers; find rational lattice vector
yv=y/ (RA[0]@G@y if False else 1)
# solve for y in coordinates: we want z (8 rationals) with z.G.r = 3Y; express via y already; rationalize
z=[Fraction(v).limit_denominator(1000) for v in y]
den=np.lcm.reduce([f.denominator for f in z]); zi=[int(f*den) for f in z]
print('charge direction (scaled by',den,'):',zi, ' pairings check:',sorted({int(np.array(zi)@G@RA[ch]) for ch in CH[0][0].values()}))
def chosen(g,steps):
    for ch in CH[g]:
        hu=RA[ch[('u',0)]]-RA[ch[('Q',0,1)]]; hd=RA[ch[('d',0)]]-RA[ch[('Q',0,-1)]]; he=RA[ch['e']]-RA[ch[('L',-1)]]
        if (ip(hu,hu)//2,ip(hd,hd)//2,ip(he,he)//2)==steps: return ch
rep={0:chosen(0,(1,1,2)) or CH[0][0],1:chosen(1,(1,2,2)),2:chosen(2,(1,2,2))}
out={'gram':G.tolist(),'colour_roots':[RA[a].tolist(),RA[b].tolist()],'weak_root':RA[w].tolist(),
     'extra_A1_roots':[RA[x].tolist() for x in ext],'time_vector':t.tolist(),'charge_direction_scaled':zi,'charge_scale':int(den),
     'sector_roots':[RA[x].tolist() for x in sorted(S)],
     'placement':{str(['(0,1)','(1,0)','(1,1)'][g]):{(k if isinstance(k,str) else '_'.join(map(str,k))):RA[v].tolist() for k,v in rep[g].items()} for g in range(3)}}
json.dump(out,open('/root/tierpy/sector_data.json','w'),indent=1)
print('sector roots',len(out['sector_roots']),'weak root',out['weak_root'],'extra',out['extra_A1_roots'],'t',out['time_vector'])
