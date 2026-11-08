# PMFlavor — open work (todo)

Checked mathematics and the downstream handoff are in [`OVERVIEW.md`](OVERVIEW.md).
This file is only what remains. Paper IV builds clean; run `./build.sh PMFlavor`
for current counts.

## Closed geometry

The flavour sector is no longer an open angle-fitting problem.

* The original Paper IV CKM formulae are formalized in `FlavourInvariants`:
  `s12 = π/(ν−χ)`, `s13 = 1/(χ α⁻¹ + π)`, `|Vcb| = (π+χ)/(α⁻¹−Dπ)`,
  `δCP = arctan(σ/χ)`.
* The PMNS bulk-strain and colour-remainder geometry is formalized in
  `PMNSGeometry`: `sin²θ23 = (1/χ)(1+π/(ν+σ))`,
  `sin²θ13 = (σ−χ)/α⁻¹`, with the upper-octant and `sin δ < 0` branches explicit.
* The golden ratio is derived from pentagon Ptolemy in `GoldenGeometry`, and an
  explicit 600-cell pentagon with edge `1/φ`, diagonal `1` and ratio `φ` is in
  `SixHundredCell`.  Hence `sin²θ12 = 1/(2φ)` follows from the 5-fold geometry.
* `α⁻¹` is imported from `PMSubstrate.geometricIndex`; it is a substrate constant,
  not a flavour input.
* Path/cycle operators and selection scans were exploratory.  They are not the
  primary derivation and are no longer kept as separate documents.

## Open items

### 1. Physical wall anchor `(δ, ε)`

`BreakingPhase` records `δ = phase mismatch`, `ε = cost`, and `ExceptionalWall`
is the mixing exceptional curve.  `PhysicalWall = 0<δ ∧ 0<ε<2` and
`physicalWall_off_exceptional` proves any physical wall point lies off the curve.
The numerical `δ, ε` remain wall inputs.

### 2. CP sign and octant orientation

`PMNSGeometry` fixes the `sin δ < 0` and upper-octant branch by definition:
`selectedCPBranch = negativeSin`, `selectedOctant = upper`.
What is still missing is the substrate orientation that selects this branch.
Do not replace it with a fit.

### 3. Per-step maintenance contract

`LeptonAxisRestriction` proves the per-cycle (three-step) contract.  A per-step
(one-step) contract needs exact within-step state restoration; the gap is
documented there.  This is the deepest remaining structural proof.

### 4. Carrier-current identification

`WeakCurrentBridge` proves the native current's chiral projector is Paper II's
weak V−A projector.  Remaining physical inputs: the flavour generator, carrier
charge values, mediator/statistics, and the chiral representation itself.

### 5. Data module

`FalsifiablePredictions.prediction_ledger` is the auditable input.  Measurements
with provenance, uncertainties and covariance belong outside the axiom-checked
tree.  Do not put measured numbers into theorem statements.

### 6. Wall masses / dispersion

`WallMassRatio.wall_coupling_ratio_of_mass_ratio` fixes the coupling ratio
`y² = (25/336)δ²`, and `WallDispersion` records `E=√(p²+m²)`.  The absolute wall
masses and physical momentum remain inputs.  `WallImpedanceChoice` separates the
capacity mass-ratio impedance from the physical energy-ratio diagnostic.

## Suggested order

1. Item 2: substrate orientation for the CP sign/octant branch.
2. Item 3: per-step restoration, if a new structural principle is available.
3. Item 1: wall anchor `(δ, ε)` once the wall dynamics fixes them.
4. Items 4 and 6: physical carrier/wall inputs.
5. Item 5: data work, kept outside the theorem tree.

Do not reopen cycle-weight scans and do not fit `V`.

## Verification

Run `./build.sh PMFlavor`.  No Paper V–VI imports; permitted axioms
`propext`, `Classical.choice`, `Quot.sound`.
