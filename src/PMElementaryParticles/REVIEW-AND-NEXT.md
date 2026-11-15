# PMElementaryParticles — open work

### A3. Three-body phase-space factorization
The three-body measure is used but not factored. Target: factor it into
(pair invariant mass) × (pair angular measure) × (spectator energy), and derive the
`MassiveDaughterSpectrum` density `pair_density` as a *consequence* rather than an
input. This is the concrete mathematical content of former review item 2.
Uses the two-body phase-space result.

### A4. Massive neutrino pair (extend the daughter spectrum) — optional/blocked
`MassiveDaughterSpectrum`/`MassiveWidth` treat a massless neutrino pair. Target:
extend `pair_density`/`closed_width` to a massive neutrino pair (at least equal
masses or one massive leg), with positivity and endpoint limits, reusing the
transported pair tensor with `q² ≠ 0`. Closed form or a controlled integral.

### A5. Rotation invariance of the continuum angular average — optional/blocked
`ContinuumPair` proves moments and linearity on *continuous* test functions but not
full rotation invariance for every integrable test function. Target: prove the
uniform-sphere average is invariant under rotations on `L¹` (change of variables /
Haar invariance of the sphere), so the pair tensor's covariance is a consequence of
the measure, not only of degree-≤2 moments.

## Elementary interactions and protocols

- **Species masses over the wire.** The wire gives every charged sector `M = D_R (δ_O + cyc κ_O)`
  and treats species alike (OVERVIEW, "Species masses over the wire"). Down quarks fit the node rule
  (`9%`, one free `d`); up quarks and charged leptons need light carriers `12`–`40×` and `5`–`80×`
  smaller. Derive from the protocols what each species occupies and how it routes over the wire:
  channel count (colour carriers three-fold, lepton-axis one-fold, `PMConstants.CarrierRepresentation`),
  series versus parallel routes (`PMSubstrate.ProtocolToll`: parallel admittances add, so a smaller
  carrier points to routes in series), node handoffs per round trip, and the leptons' on-axis
  geometry. Relate to the existing tier ledgers (`TierLedger.tiersFor`: up `{0, 2, 3}`, down and
  lepton `{0, 1, 2}`; `QuarkMasses`, `LeptonMasses`). Do not match the required factors to
  constants; derive them and test on up quarks and leptons together. Constraint from the CKM
  (PMFlavor OVERVIEW, negative result; `tools/wire_ckm_scan.py`): no choice of light carriers in the
  wire's mass form fits the quark masses and the CKM together, so protocol carriers alone cannot
  close the quark sector; this item depends on the PMFlavor reading question (`U_uᴴ J U_d` or a
  mass-form change) being settled first. Includes the old
  tier item: derive the routing histories and rates, their costs, and the tiers each protocol occupies; the
  lepton and quark ledgers still need a cost or selection rule for assigning invariants to tiers.
  Upstream: PMAction, "Size of the other wall's detuning".
- Connect the charged-current operator to the contact vertex in `AmplitudeTrace`. Identify the external carrier states, physical mode weights, and readout normalization.
- Supply the physical tick calibration for `DecayLaw`. Identify the low-energy radiative contribution for elementary widths.
- Determine the physical finite-channel replacement for the muon continuum phase space. For the tau total width, the electronic branching fraction remains an input; hadronic channels depend on [PMHadrons](../PMHadrons/REVIEW-AND-NEXT.md).
- A neutrino-decay prediction requires a physical channel and mass ordering. The corresponding cosmological propagation question is tracked in PMCosmology.
