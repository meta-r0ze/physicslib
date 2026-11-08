# Geometry review: the original flavour formulae

The original Paper IV calculation already derives the flavour angles from
transition geometry, not from a fitted mass matrix.  This is the primary
structure and should be the target of any operator model.

## CKM: boundary leak / topological knots

```text
s12 = π/(ν − χ) = π/14
s13 = 1/(χ α⁻¹ + π)
|Vcb| = (π + χ)/(α⁻¹ − Dπ)
δCP = arctan(σ/χ)
```

Numerical angles:

```text
θ12 ≈ 12.97°
θ13 ≈ 0.207°
θ23 ≈ 2.367°
δCP ≈ 68.20°
```

The paper's validation records pulls of roughly `0.11σ`, `1.06σ`, `0.17σ`,
`0.04σ` for these entries.

## PMNS: bulk phonons / capacity promotion

```text
sin²θ12 = 1/(2φ)                 (H4 / 600-cell golden aperture)
sin²θ23 = (1/χ)(1 + π/(ν+σ))     (maximal bisection + bulk strain)
sin²θ13 = (σ − χ)/α⁻¹            (colour-remainder cross-talk)
δCP from |U_μ2| = |U_τ2|         (reference persistence sum rule)
```

Numerical angles:

```text
θ12 ≈ 33.77°
θ13 ≈ 8.51°
θ23 ≈ 49.30°
δCP ≈ 220.8°  (sin δ < 0 branch)
```

The paper records pulls of roughly `0.42σ`, `0.64σ`, `0.05σ`, `0.88σ`.

## What this means for the operator route

The path/cycle operator is a **candidate microscopic realisation**, not the
primary derivation.  The paper's logic is aperture-first:

```text
transition geometry fixes the admittance
→ mass spectrum self-organises to satisfy it
```

not:

```text
choose a mass matrix
→ diagonalise
→ read off the mixing
```

So the operator should be checked against the geometric apertures above.

## Current operator comparison

CKM path operator:

```text
operator: (11.39°, 0.084°, 2.73°)
geometry: (12.97°, 0.207°, 2.367°)
```

PMNS best cycle candidate:

```text
operator: (28.84°, 7.89°, 49.12°)
geometry: (33.77°, 8.51°, 49.30°)
```

The CKM operator is a reasonable realisation.  The PMNS cycle candidate fixes
`θ23` and `θ13` but misses `θ12`; the H4 golden aperture is better than the
operator.

## Remaining genuine inputs

```text
φ        derived from pentagon Ptolemy; explicit 600-cell pentagon now in SixHundredCell
α⁻¹      imported from PMSubstrate.geometricIndex (substrate, not flavour input)
CP sign  fixed by the sin δ < 0 branch
octant   tied to the reference sum rule, not independently derived
```

## Next check

The regular-pentagon Ptolemy relation `d²=1+d` derives `d=φ` and hence
`sin²θ12=1/(2φ)` in `GoldenGeometry.lean`.  `SixHundredCell.lean` now places an
explicit five-vertex pentagon in the 600-cell coordinates: edge `1/φ`, diagonal
`1`, ratio `φ`, with the scaled Ptolemy relation proved.
