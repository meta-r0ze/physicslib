"""Which costs on the protocol label can give the Toll order nu < e < d < u?

Label = a carrier of the other D4 factor (EP OVERVIEW, "Protocol register"). Read in a
spinor-class frame, the four gauge orbits are nu = (+,+,+,+)/2, e = -nu, u = x0 = +1/2 with
two of x1..x3 flipped, d = -u. Colour (permutations of axes 1..3) leaves only two linear
invariants, x0 and S = x1 + x2 + x3. Targets: s = 0.030, 0.087, 0.26, 1.14 (k = alpha/2).
"""
import itertools, numpy as np
h = 0.5
nu = np.array([h, h, h, h]); e = -nu
u = np.array([h, -h, -h, h]); d = -u          # one representative per colour orbit
orb = {"nu": nu, "e": e, "d": d, "u": u}
inv = lambda w: (w[0], w[1:].sum())             # colour-symmetric linear invariants
print("invariants (x0, S):", {k: inv(w) for k, w in orb.items()})

# 1. no monotone function of any linear invariant a*x0 + b*S gives nu < e < d < u
hits = 0
for t in np.linspace(0, 2*np.pi, 3600, endpoint=False):
    a, b = np.cos(t), np.sin(t)
    L = [a*inv(orb[k])[0] + b*inv(orb[k])[1] for k in ("nu", "e", "d", "u")]
    hits += all(L[i] < L[i+1] for i in range(3))
print("directions (a,b) ordering nu<e<d<u:", hits, "of 3600")

# 2. sign-blind (even) invariants tie the weak partners: quadratic forms see w and -w alike
print("even forms tie partners: x0*S, S^2 equal on nu,e and on u,d:",
      [round(f(orb["nu"]) - f(orb["e"]), 9) == 0 and round(f(orb["u"]) - f(orb["d"]), 9) == 0
       for f in (lambda w: inv(w)[0]*inv(w)[1], lambda w: inv(w)[1]**2)])

# 3. so the cost needs an odd part and an even part; log s = a x0 + b S + c S^2 + const fits
s = dict(nu=0.030, e=0.087, d=0.26, u=1.14)
A = np.array([[inv(orb[k])[0], inv(orb[k])[1], inv(orb[k])[1]**2, 1] for k in s])
coef = np.linalg.solve(A, np.log(list(s.values())))
print("log s = a x0 + b S + c S^2 + const: a, b, c, const =", np.round(coef, 3), "(4 numbers for 4: a fit)")

# 4. the crossing carries no label holonomy: triality has order three on the nose
M = np.array([[1, 1, 1, -1], [1, 1, -1, 1], [1, -1, 1, 1], [1, -1, -1, -1]]) / 2
print("triality^3 = identity:", np.allclose(np.linalg.matrix_power(M, 3), np.eye(4)))
print("fixed plane of triality:", "contains no vector weight (it maps class v to class s)")

# 5. the up protocol relative to the bare wire: effective node coupling k_eff = (m2/m3)/sqrt(3/2)
alpha = 1/137.036
for name, r in dict(nu=0.17, e=0.0595, d=(0.019, 0.022), u=(0.0036, 0.0042)).items():
    r = np.atleast_1d(r)
    print(f"  {name}: k_eff / (alpha/2) =", np.round(r/np.sqrt(1.5)/(alpha/2), 2))

# 6. shape of the targets: a geometric ladder in the order u, d, e, nu
n = np.arange(4)
for de in (2.7, 3.2):
    for ue in (12, 13.5):
        y = np.log([0.087*ue, 0.087*de, 0.087, 0.030])
        sl, ic = np.polyfit(n, y, 1)
        res = y - (ic + sl*n)
        print(f"  s_d/s_e={de}, s_u/s_e={ue}: step ratio {np.exp(-sl):.2f}, rms log residual {np.sqrt(np.mean(res**2)):.3f}")
print("  (alpha^-1/4 = 3.42 and 3 both fit the step; the data do not separate them)")

# 7. orientation from the clock: lepton (reference) axis = clock axis 0. Forward root events raise the
#    clock coordinate (PMAction.SliceHop: a -1 clock event runs the clock backwards). Label moves are
#    root shifts landing on a vector carrier (all colours), optionally forward-only.
import heapq
E = np.eye(4, dtype=int)
car = [s_*E[j] for j in range(4) for s_ in (1, -1)]
key = lambda w: tuple(int(x) for x in w)
roots = [s_*E[a] + t*E[b] for a in range(4) for b in range(a+1, 4) for s_ in (1, -1) for t in (1, -1)]
name = {key(E[0]): "nu", key(-E[0]): "e"}
for j in (1, 2, 3): name[key(E[j])] = "u"; name[key(-E[j])] = "d"
U = {key(E[j]) for j in (1, 2, 3)}
for lbl, allow in [("all roots", lambda r: True), ("forward only", lambda r: r[0] >= 0)]:
    G = {key(w): [key(w + r) for r in roots if allow(r) and key(w + r) in {key(c) for c in car}] for w in car}
    D = {}
    for st in G:
        pq, seen = [(0, st)], set()
        while pq:
            dd, x = heapq.heappop(pq)
            if x in seen: continue
            seen.add(x)
            if x in U: D[st] = dd; break
            for y in G[x]: heapq.heappush(pq, (dd + 1, y))
    out = {}
    for k_, v in D.items(): out.setdefault(name[k_], set()).add(v)
    print(f"  root shifts to reach u ({lbl}):", out, "unreachable:", {name[k_] for k_ in G if k_ not in D})
print("  -> no ladder: d reaches u through another colour, e in one forward event")
