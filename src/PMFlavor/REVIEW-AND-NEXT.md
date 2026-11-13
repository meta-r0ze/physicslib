# PMFlavor — open work (todo)

Checked mathematics and the downstream handoff are in [`OVERVIEW.md`](OVERVIEW.md).
This file is only what remains. Paper IV builds clean; run `./build.sh PMFlavor`
for current counts.

The flavour derivation (mixing formulas, angles, octants, CP magnitude, mass ratios,
breaking direction, carrier-current objects) is derived or E8-sourced; see
`OVERVIEW.md`. The **CP-sign branch** is a *no-go*, not a gap:
`ReferenceFlavour.conjugate_cost_tie` proves any cost depending only on the mixing
squared-moduli is `u ↦ ū`-invariant, so the two branches **tie** and a symmetric cost
cannot pick a sign — the continuous-symmetry case of
`PersistenceMechanics.SelectionSymmetry`. The branch is symmetry-breaking (the
reference orientation, `ChiralityConvention.Orientation.referenceOrientation`).

## Open items

The numerals in the flavour formulas are derived invariants (`FlavourInvariants`), `φ` is derived
(`GoldenGeometry`), and the CP sign is a proven tie. What is still open (Nov 2026):

### 1. The six functional forms are ansätze

`s₁₂ = π/(ν−χ)`, `s₁₃ = 1/(χα⁻¹+π)`, `|V_cb| = (π+χ)/(α⁻¹−Dπ)`, `δ_CP = arctan(σ/χ)`,
`sin²θ₁₂ = 1/(2φ)`, `sin²θ₂₃ = (1/χ)(1 + π/(ν+σ))`, `sin²θ₁₃ = (σ−χ)/α⁻¹`. Each evaluates
derived invariants, but the form (which invariants, combined how) is supplied. This is the main
derivation gap of Paper IV.

### 2. The `687/688` first-row dressing

`PMConstants.FlavourDressing` identifies `1/688` as the per-direction reference deficit
`(1−η)/D`; the claim that the CKM first row inherits it is the model step.

### 3. The V−A projector off the kernel

`PMAction.ChiralityConvention.projector_unique_on_kernel` forces the projector on the zero
kernel; attaching the weak gauge representation and extending it off the kernel are inputs.

### 4. Inputs that are not derivable

* **Wall anchor magnitude `δ` (and `ε`).** `BreakingPhase` records `(δ, ε)`; the direction
  (lepton axis) and functional form are E8 (`MixingMatrix.rootP/rootM_eq_substrate`), the
  magnitude has no cost functional. Anchors: `TransferFlavor.unitWall`, `ckmWall` (`χ/ν`).
* **Absolute wall-mass scale.** The ratios are E8 (`WallMassRatio.capacity_ratio_sq`,
  `coupling_ratio`); the absolute scale is the usual external unit, like `m_e`.
* **Octant running.** Paper IV's "running resolves the octant anomaly" has no Lean statement.

## Modelling boundary

The carrier statistics are now derived in `PMAction.CarrierStatistics` (a `2π` turn
is `−1`, `exchange_is_minus_one`, `exclusion`). Realizing the reference-stabilizer
mediator in a physical interaction is still a modelling boundary (like the Yang–Mills
scope note), not a missing theorem. Do not reopen cycle-weight scans and do not fit `V`.

## Verification

Run `./build.sh PMFlavor`. No Paper V–VI imports; permitted axioms
`propext`, `Classical.choice`, `Quot.sound`.
