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

`WolfensteinOctant` proves the octants (lower solar, upper atmospheric, small
reactor) as consequences of the supplied closed forms, and `PMNSGeometry` fixes
`selectedCPBranch = negativeSin` by definition. The CP sign is now known to be
genuinely external: `ReferenceFlavour.column2_difference_conj` proves the
persistence balance `|U_μ2| = |U_τ2|` depends only on `cos δ`, so `δ` and `−δ`
satisfy it equally. The sum rule fixes `cos δ` (hence `|δ|`), not the branch.
`Downstream.PMNS.jarlskog_sign_iff_branch` closes the remaining apparent loophole:
the leptonic Jarlskog is exactly `(positive angle product) · sin δ`, so
`J ≤ 0 ↔ sin δ ≤ 0` and `jarlskog_nonpos` is the branch choice in disguise, not
independent evidence. `ReferenceFlavour.ckm_normSq_conj` shows every mixing
probability `|V_ij|²` is invariant under `u ↦ ū` (`δ ↦ −δ`), so no mixing datum
selects the branch either — only the Jarlskog (CP violation) does. What is still
missing is the substrate orientation that selects `sign(sin δ)`; that is exactly
what the mixing/octant/Jarlskog statements cannot supply. Do not replace it with a
fit.

### 3. Per-step maintenance contract

`LeptonAxisRestriction` proves the per-cycle contract; `PerStepContract` now
formalizes the per-step one. `run_roots_axis_zero` derives `R 0 = 0` for
*every* event in a run whose each step restores the reference, and
`sampleEvent_pair_not_maintained` closes Gap A — the involution bypass that a
cycle-end-only check admits. What remains is physical, not Lean-structural:
deriving the per-step restoration (exact within-step state restoration) from
the actual update dynamics instead of assuming it.

### 4. Carrier-current identification

Derived: `WeakCurrentBridge` fixes the native current's chiral projector as Paper
II's `P_L` (`ChiralityConvention.projector_eq_fromBlocks_PL` does so globally), and
the flavour doublet generators are Paper II's — `FlavourCurrent.upstream_raising`
(charged `T₊`) and `FlavourCurrent.neutral_charge_values` (neutral `T₃ = ±1/2`).
So the "flavour generator" and "carrier charge values" are the doublet
representation, not free. Remaining physical inputs: attaching that representation
to the physical weak interaction, the mediator/statistics, and the chiral
representation's physical gauge content.

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

Ordered substrate-first: derive each apparent input from E8 where possible, then
treat only the residue as a model input.

1. Item 4: carrier-current identification — the substrate owns the channels,
   charges and current; the charged generator and chirality are already derived.
2. Item 1: wall anchor `(δ, ε)` — a single lepton-axis weight on the substrate link.
3. Item 2: the substrate orientation selecting `sign(sin δ)` — mixing
   probabilities are branch-blind (the remaining external step).
4. Item 3: per-step restoration from the actual update dynamics.
5. Item 6: wall masses / dispersion — the ratio is E8; the scale is the input.
6. Item 5: data work, kept outside the theorem tree.

Do not reopen cycle-weight scans and do not fit `V`.

## Verification

Run `./build.sh PMFlavor`.  No Paper V–VI imports; permitted axioms
`propext`, `Classical.choice`, `Quot.sound`.
