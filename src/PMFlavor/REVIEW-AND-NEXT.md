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
is the mixing exceptional curve. `PhysicalWall = 0<δ ∧ 0<ε<2` (the `2` is `χ`) and
`physicalWall_off_exceptional` proves any physical wall point lies off the curve.
The curve's constants are E8, not free: `MixingMatrix.rootP/rootM_eq_substrate`
give `root±(x) = (σ + x ± √((x−1)² + Dχ))/2`, and `rootMInv_eq_substrate` gives
`((y−1)(D−y))/((σ−χ)−y)` — the block numerals `5,8,4,3` are `σ, Dχ, D, σ−χ`.
The remaining input is the *magnitude* `δ` of the S₃-breaking (the lepton-axis
self-coupling): the symmetric substrate link has `δ = 0`. Two anchors are
recorded — `TransferFlavor.unitWall` (`δ = ε = 1`) and the E8-proposed
`TransferFlavor.ckmWall` (`δ = ε = χ/ν = 1/8`, with `ckmWall_physical`). Which is
physical is the remaining model choice; the curve, range and eigenvalues are E8.

### 2. CP sign and octant orientation

`WolfensteinOctant` proves the octants (lower solar, upper atmospheric, small
reactor) as consequences of the supplied closed forms. `PMNSGeometry.selectedCPBranch`
now reads the branch off the **substrate orientation object**
`PMAction.ChiralityConvention.Orientation.referenceOrientation` (the reference's
chirality, `reference_proj`; the wall exchange swaps the two orientations). So the
CP sign is the substrate's left/right convention, not a flavour fit. It is also
not derivable from the data: `ReferenceFlavour.column2_difference_conj` proves the
persistence balance `|U_μ2| = |U_τ2|` depends only on `cos δ`, so `δ` and `−δ`
satisfy it equally. The sum rule fixes `cos δ` (hence `|δ|`), not the branch.
`Downstream.PMNS.jarlskog_sign_iff_branch` closes the remaining apparent loophole:
the leptonic Jarlskog is exactly `(positive angle product) · sin δ`, so
`J ≤ 0 ↔ sin δ ≤ 0` and `jarlskog_nonpos` is the branch choice in disguise, not
independent evidence. `ReferenceFlavour.ckm_normSq_conj` shows every mixing
probability `|V_ij|²` is invariant under `u ↦ ū` (`δ ↦ −δ`), so no mixing datum
selects the branch either — only the Jarlskog (CP violation) does. What is still
missing is only the convention `left ↔ negativeSin` itself, which is now a single
upstream object rather than a flavour choice. Do not replace it with a fit.

### 3. Per-step maintenance contract

`LeptonAxisRestriction` proves the per-cycle contract; `PerStepContract` now
formalizes the per-step one. `run_roots_axis_zero` derives `R 0 = 0` for
*every* event in a run whose each step restores the reference, and
`sampleEvent_pair_not_maintained` closes Gap A — the involution bypass that a
cycle-end-only check admits. The per-step restoration itself is PM-2's
`ReferenceMaintenance.live_restored`/`canonical_restores`: one canonical
maintenance pass restores the live reference for every initial discrepancy. What
remains is the model identification — encoding the packet reference as the
maintained register/record bit — not a new Lean obligation. (So the per-step
condition is not free; it is PM-2's maintenance theorem transported.)

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

`FalsifiablePredictions.prediction_ledger` is the auditable input. Measurements
with provenance, uncertainties and covariance belong outside the axiom-checked
tree. **Verified:** no derivation module imports the comparison leaves
(`FlavourPulls`, `ExperimentalPulls`); only the top-level `PMFlavor.lean`
aggregator does, so no measured number enters the derivation closure. Do not put
measured numbers into theorem statements.

### 6. Wall masses / dispersion

Both ratios are E8: `WallMassRatio.capacity_ratio_sq` gives `256/441 = (ν/(ν+σ))²`
and `coupling_ratio` gives `25/336 = σ²/(ν(ν+σ))`; `wall_coupling_ratio_substrate`
restates the coupling law `y² = σ²/(ν(ν+σ)) δ²` in those terms. `WallDispersion`
records `E=√(p²+m²)`. The remaining input is the absolute wall-mass scale and
physical momentum (the usual unit/anchor input, like `m_e`). `WallImpedanceChoice`
separates the capacity mass-ratio impedance from the physical energy-ratio
diagnostic.

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
