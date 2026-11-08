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

**Status (latest pass).** Items 2 and 3 are **closed** upstream: the CP branch is
the substrate orientation object (`ChiralityConvention.Orientation`), and the
per-step restoration is `SectorObligations.refresh_exact` (per-tick reference
refresh), with no flavour-side choice left. Items 1, 4 and 6 are reduced to
explicit, named inputs (wall anchor, physical weak attachment, mass scale); item 5
is a verified data separation. The flavour-specific derivation work is complete;
what remains are the upstream objects/identifications those notes name.

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
**Provenance:** the breaking *direction* (lepton axis) and functional form are E8;
the *magnitude* is neither E8-forced nor persistence-selected (there is no cost
functional in `δ`), so it is a genuine model input.

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
selects the branch either — only the Jarlskog (CP violation) does. **Closed:** the
branch is `ChiralityConvention.Orientation.referenceOrientation`, so the only
residue is the substrate convention `left ↔ negativeSin`, owned upstream, not a
flavour fit.

### 3. Per-step maintenance contract

`LeptonAxisRestriction` proves the per-cycle contract; `PerStepContract` formalizes
the per-step one (`run_roots_axis_zero`, `sampleEvent_pair_not_maintained`,
`perCycle_does_not_imply_perStep`). The per-step restoration is **derived
upstream**, not assumed: PM-2 `ReferenceMaintenance.live_restored` (one canonical
pass restores the live reference) and, at the record level,
`PMConstants.SectorObligations.refresh_exact` / `refresh_exact_homogeneous` — with
lattice-translation (or any homogeneous record-moving) routing and a stationary
background, the coupling site's reference is restored *at every tick*. So the
per-step condition is a theorem; the only residue is naming the packet reference
as the coupling-site record.

### 4. Carrier-current identification

Derived: the chiral projector is Paper II's `P_L` (`WeakCurrentBridge`, and
`ChiralityConvention.projector_eq_fromBlocks_PL` globally); the flavour doublet
generators are Paper II's (`FlavourCurrent.upstream_raising` charged `T₊`,
`neutral_charge_values` neutral `T₃ = ±1/2`); and the doublet is attached to the
reference — `PMConstants.ReferenceStabilizer.electroweak_stabilizer` shows the
reference carries `su(2)` and leaves exactly `Q = T₃ + Y/2` unbroken
(`weakGen A (lepton s) (lepton t) = A s t`). So the "flavour generator", "carrier
charge values" and the weak representation attachment are the doublet, not free.
**Provenance of the rest:** both are E8. Spin–statistics is the substrate carrier
parity — `PMAction.CarrierParity.range_iff_odd`/`carrier_exchange_parity` identify
the physical carrier sector exactly with the antipodal-odd (`−1`) eigenspace. The
mediator is the broken electroweak direction of the reference —
`PMConstants.ReferenceStabilizer.mediator_moves_reference` (the stabilizer is
exactly the `Q` line). What remains is only the dynamical attachment/statistics
law, not the objects.

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
physical momentum. **Provenance:** neither E8 nor persistence — it is the usual
unit/anchor input (like `m_e`), fixed externally by comparison, not derived. `WallImpedanceChoice`
separates the capacity mass-ratio impedance from the physical energy-ratio
diagnostic.

## Suggested order

Ordered substrate-first: derive each apparent input from E8 where possible, then
treat only the residue as a model input. Flavour-side work is done; the remaining
line items are the upstream objects/identifications the notes name.

1. Item 2 — **closed** (branch = substrate orientation).
2. Item 4 — generator/charges derived; physical weak attachment/mediator upstream.
3. Item 1 — curve/range/eigenvalues E8; anchor magnitude is the model input.
4. Item 6 — ratios E8; only the scale/momentum anchor remains.
5. Item 3 — per-step = PM-2 `live_restored`; packet↔record is a model bridge.
6. Item 5 — data, kept outside the theorem tree.

Do not reopen cycle-weight scans and do not fit `V`.

## Verification

Run `./build.sh PMFlavor`.  No Paper V–VI imports; permitted axioms
`propext`, `Classical.choice`, `Quot.sound`.
