#!/usr/bin/env python3
"""Independent full-state sample validation of phase_gate_census.cpp.

Run: python3 tools/test_phase_gate_census.py OUTPUT.csv
The simulation detects first return directly. It does not use the C++ path/parity
shortcut. This validates computation, not a kernel-certified census.
"""
import random,csv,math,sys
rng=random.Random(20261127)
def run(n,S,phase=0,d=0,x=0,m=0):
    initial=(phase,d,x,m); R=D=0
    for T in range(1,86*n+173):
        turn=phase in S; d^=turn; R+=turn; m^=1<<x
        v=1-2*d; D+=v; x=(x+v)%n; phase=(phase+1)%43
        if (phase,d,x,m)==initial:return T,R,D
    raise AssertionError('no return')
count=0
for n in [3,5,7,9,11,13,43]:
    for i in range(160):
        mask=rng.randrange(1<<22)
        S=({0} if mask&1 else set())|{t for j in range(1,22) if mask>>j&1 for t in [j,43-j]}
        d=0; drift=0
        for t in range(43):d^=t in S;drift+=1-2*d
        g=len(S)
        T=(86 if drift%n==0 else 172) if g%2 else 86*n//math.gcd(n,abs(drift))
        disp=0 if g%2 else 2*n//math.gcd(n,abs(drift))*drift
        got=run(n,S,m=rng.randrange(1<<n))
        assert got==(T,T*g//43,disp),(n,S,got,T,disp)
        count+=1
    for phase in range(43):
        for d in [0,1]:
            T,R,D=run(n,{0},phase,d,rng.randrange(n),rng.randrange(1<<n))
            assert (T,R,D)==((86,2,0) if n==43 else (172,4,0))
            count+=1
with open(sys.argv[1]) as f: rows=list(csv.DictReader(f))
for n in [3,5,7,9,11,13,43]:assert sum(int(r['programs']) for r in rows if int(r['n'])==n)==2**22
print(f'{count} independent full-state simulations passed; {len(rows)} census rows cover 2^22 gate sets per n')
