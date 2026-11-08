# Flavor selection tests

Exploration only.  These are numerical capability tests, not E8 predictions and
not frozen comparison data.

Targets used qualitatively:

```text
CKM : θ12 ≈ 13°, θ13 ≈ 0.2°, θ23 ≈ 2.4°
PMNS: θ12 ≈ 34°, θ13 ≈ 8.5°, θ23 ≈ 49°
```

## 1. Operator-valued mass matrix

Model:

```text
M² = diag(m_i²) + w · adjacency
```

Tested path and complete adjacency.

Result:

```text
path graph      can reach CKM-like and PMNS-like angle patterns
complete graph  does not reach either pattern cleanly
```

A random capability search found:

```text
path → CKM : (12.7°, 0.19°, 2.38°)
path → PMNS: (33.9°, 7.97°, 46.8°)
```

with different mass/weight parameters for the two sectors.

Verdict: **viable, but not yet a derivation.**  The path graph has enough
structure to produce both patterns; the parameters still have to come from
capacity/link weights.

## 2. Graph mode law

```text
CKM  = boundary conduction → path graph
PMNS = capacity promotion  → complete graph
```

The complete graph did **not** work as the PMNS sector.  It tends to produce
either small angles or too-large θ23.

Verdict: **the simple mode-to-topology identification fails.**  Both sectors
behave more like path-type operators with different mass hierarchies and link
weights.

## 3. Holonomy/flux

A single cycle flux produces a nonzero Jarlskog invariant:

```text
δ = 30° → J ≈ 1.7×10⁻²
δ = 60° → J ≈ 2.9×10⁻²
δ = 90° → J ≈ 3.3×10⁻²
```

Verdict: **holonomy can supply the CP phase, but not the angles.**  It is a
phase-sector ingredient, not a full `V` selection law.

## 4. Pointer/decoherence selection

If the environment covariance is a substrate operator `C_env`, the pointer basis
is its eigenbasis:

```text
V = eigenvectors(C_env)
```

This is mathematically the same as the operator-valued mass-matrix route.  It
does not add an independent selection principle unless `C_env` is derived
separately.

Verdict: **not independent.**

## 5. Persistence/return functional

Needs a concrete wall Hamiltonian and tick.  Not tested here; without those it
is equivalent to choosing a basis by hand.

Verdict: **deferred.**

## 6. Texture zeros

Approximate observed matrices:

```text
CKM : two entries below 0.01
PMNS: no entries below 0.1
```

Verdict: **texture zeros can help the CKM sector, but not PMNS.**  They are a
constraint, not a selection law.

## 7. Finite symmetry representation

The simplest A4/tribimaximal pattern has

```text
θ13 = 0
```

which is ruled out by the observed nonzero θ13.

Verdict: **plain A4 is excluded.**  A finite group would need a controlled
breaking that generates θ13.

## Overall

The only viable route found is:

```text
mass matrix = path-type substrate operator
V = its eigenbasis
```

The next task is to derive the path link weights from:

```text
capacityImpedance = 16/21
transferImpedance
ν, σ, Δ
```

Do not fit the masses or weights to CKM/PMNS.
