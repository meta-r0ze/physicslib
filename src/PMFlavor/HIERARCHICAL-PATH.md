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

## Characteristic polynomial

`HierarchicalOperator a b c` has the generic characteristic polynomial

```text
x³ − ((8(a+b+c)+37)/8)x²
   + ((16ab+16ac+58a+16bc+37b+53c+63)/16)x
   − ((16abc+21ab+37ac+21a+16bc+21b+21c)/16).
```

This is proved in `HierarchicalPathOperator.charpoly_eq`.

## Separate PMNS mass term

The PMNS sector uses a different wall-mass diagonal at `δ=1`, `y=1`:

```text
m_low²  = massSqM 1 1 ≈ 0.3819660
m_high² = massSqP 1 1 ≈ 2.6180340
```

with a degenerate light pair:

```text
D_PMNS = diag(m_low², m_low², m_high²).
```

Numerical eigenbasis gives:

```text
θ12 ≈ 35.35°
θ13 ≈ 9.40°
θ23 ≈ 35.07°
```

This is PMNS-like for `θ12` and `θ13`, but `θ23` is low compared with
`≈49°`.  It is a separate operator from the CKM diagonal; the CKM diagonal is
not reused.
