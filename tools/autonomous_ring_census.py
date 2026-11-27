#!/usr/bin/env python3
"""Exhaust all one-packet stream/marker cycles; this is not a Lean certificate.

Implements AutonomousCensus.packet_formula, with False=forward, True=backward.
Every position, direction and n-bit marker word is included. Perturbations are
checked at every orbit phase. Report support; do not silently choose a
localization cutoff. Double-occupancy variants coincide by double_flip_unseen.
"""
import argparse,csv,json,math
from pathlib import Path
from collections import Counter,defaultdict
from fractions import Fraction

def census(n,k):
 N=(1<<n)*2*n
 nxt=[0]*N; turn=[0]*N; vel=[0]*N
 for mask in range(1<<n):
  for d in range(2):
   for x in range(n):
    i=mask*2*n+d*n+x; m=(mask>>x)&1
    rev=(m if k in(0,2) else 0 if k==1 else 1-m if k==3 else 1)
    nd=d^rev; nm=mask if k==0 else mask^(1<<x)
    v=1-2*nd
    nxt[i]=nm*2*n+nd*n+(x+v)%n;turn[i]=rev;vel[i]=v
 ids=[-1]*N; cycles=[]
 for i in range(N):
  if ids[i]>=0:continue
  states=[];j=i
  while ids[j]<0:
   ids[j]=len(cycles);states.append(j);j=nxt[j]
  assert j==i
  visited=0;support=0;instant=0
  for j in states:
   mask,dx=divmod(j,2*n);x=dx%n
   visited|=1<<x;support|=mask|(1<<x)
   instant=max(instant,(mask|(1<<x)).bit_count())
  cycles.append(dict(T=len(states),R=sum(turn[j] for j in states),wind=sum(vel[j] for j in states),support=support.bit_count(),visited=visited.bit_count(),instant=instant,states=states))
 for c in cycles:
  rate=Fraction(c['R'],c['T']);robust=True
  for j in c['states']:
   for b in range(n):
    mask,dx=divmod(j,2*n)
    p=cycles[ids[(mask^(1<<b))*2*n+dx]]
    if Fraction(p['R'],p['T'])!=rate:robust=False
  c['rateRobust']=robust
 groups=Counter((c['T'],c['R'],c['wind'],c['support'],c['visited'],c['instant'],c['rateRobust']) for c in cycles)
 return dict(n=n,kind=k,states=N,cycles=len(cycles),groups=[dict(T=a,R=b,displacement=c,support=d,visited=e,instant=i,rateRobust=f,cycles=v) for (a,b,c,d,e,i,f),v in sorted(groups.items())])
def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--sizes',default='3,5,7,9,11,13')
 parser.add_argument('--delta',type=int,default=43)
 parser.add_argument('--output-dir',type=Path,required=True)
 args=parser.parse_args()
 sizes=[int(x) for x in args.sizes.split(',')]
 if any(n<3 or n%2==0 for n in sizes):parser.error('use odd sizes >=3')
 args.output_dir.mkdir(parents=True,exist_ok=True)
 out=[]; flat=[]
 for n in sizes:
  for k in range(5):
   r=census(n,k);out.append(r)
   assert sum(g['T']*g['cycles'] for g in r['groups'])==r['states']
   for g in r['groups']:
    assert g['R']%2==0 and g['displacement']%n==0
    if k==0:assert g['R'] in (0,2)
    if k==1:assert g['R']==0
    if k in (2,3):assert 2*g['R']==g['T']
    if k==4:assert g['R']==g['T']==4 and g['displacement']==0
    for double_flip in (0,1):
     row=dict(n=n,kind=k,double_flip=double_flip,**g)
     common=math.lcm(g['T'],args.delta)
     row.update(per_delta=str(Fraction(args.delta*g['R'],g['T'])),
                velocity=str(Fraction(g['displacement'],g['T'])),
                clock_return_ticks=common,
                clock_return_reversals=g['R']*(common//g['T']))
     flat.append(row)
   robust=sorted(set(str(Fraction(g['R']*args.delta,g['T'])) for g in r['groups'] if g['rateRobust']))
   print(f"n={n} kind={k}: {r['states']} states, {r['cycles']} cycles, robust averages={robust}",flush=True)
 (args.output_dir/'cycles.json').write_text(json.dumps(out,indent=2)+'\n')
 with (args.output_dir/'families.csv').open('w',newline='') as f:
  writer=csv.DictWriter(f,fieldnames=list(flat[0]));writer.writeheader();writer.writerows(flat)
 print(f"Wrote {len(flat)} family rows; each double-occupancy variant is included.")

if __name__=='__main__':main()
