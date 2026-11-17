#!/usr/bin/env python3
"""Second register brainstorm (PMElementaryParticles REVIEW, "Protocol register and coupling").
Tests: T1 32 light components per generation; T2 a 1+3 label split about the reference axis;
T3 a doublet sign; T4 label unchanged by wall terms (Map); T6 label moved by the particle's
transport (Protocol); T7 label separate from the Dirac generators (ColourRegister).
Light Dirac components per label: 2 zero modes per wall x 2 walls = 4."""
import itertools

light = 4
print("T1 counts:")
for name, labels in [("even modes of the other wall", 4), ("vector carriers: axis x sign", 8),
                     ("16 channels incl. hand (double counts the walls)", 16)]:
    print(f"  {name}: {labels} x {light} = {labels * light} (need 32)")

print("Idea: label = auxiliary axis k of the hop's root pair (2e_j = (e_j+e_k)+(e_j-e_k))")
for k in range(4):
    use = [j for j in (1, 2, 3) if j != k]
    print(f"  k={k}: serves spatial directions {use}; in the clock slice: {use if k else []}")

print("Idea: E8 glued roots = generation x protocol x wire carrier")
pure, glued = 2 * 24, 3 * 64
print(f"  E8 roots = {pure} pure (D4+D4 roots) + {glued} glued (classes v,s,c: 8 x 8 each) = {pure + glued}")
print(f"  per glue class: 8 protocol carriers (D4_1) x 8 wire carriers (D4_2) = 64; three classes = three generations")
