# Hierarchical path operator

## Diagonal mass term

At

```text
δ = χ = 2
y = σ = 5
```

the two-wall masses are

```text
m_low²  = massSqM 2 5 ≈ 0.4921894
m_high² = massSqP 2 5 ≈ 32.5078106
```

The middle entry is the E8 value

```text
m_mid² = χ² = 4.
```

So

```text
D = diag(0.4921894, 4, 32.5078106).
```

No entry is fitted to CKM/PMNS.

## Operator

```text
M = pathOperator + D
```

with `pathOperator` from `PathOperator.lean`.

## Numerical eigenbasis

Eigenvalues:

```text
1.2909261542
6.4512110311
33.8828628147
```

Eigenvectors:

```text
[[ 0.9803107311,  0.1974555909,  0.0014697055],
 [ 0.1973005259, -0.9791865452, -0.0476047504],
 [ 0.0079607083, -0.0469574214,  0.9988651699]]
```

Mixing angles:

```text
θ12 ≈ 11.39°
θ13 ≈ 0.084°
θ23 ≈ 2.73°
```

Compare:

```text
CKM  ≈ (13.0°, 0.2°, 2.4°)
```

This is a CKM-like pattern, obtained from the E8 wall masses and `χ²`, not from a
fit.

## Status

```text
hierarchical diagonal from wall masses   ✅
CKM-like mixing                          ✅ numerical
Lean eigenbasis proof                    ❌ cubic spectrum, deferred
PMNS sector                             ❌ separate operator needed
```

The PMNS sector still needs its own mass term; do not reuse the CKM diagonal.
