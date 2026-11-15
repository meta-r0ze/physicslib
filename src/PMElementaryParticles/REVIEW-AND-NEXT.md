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

- **Species masses over the wire.** The wire gives one light-mass form,
  `M = D_R (δ_O + cyc κ_O)`, and treats species alike (OVERVIEW, "Species masses over the wire").
  Derive from E8 which protocols exist and how each uses the wire: what it occupies, channel count
  (colour carriers three-fold, lepton-axis one-fold, `PMConstants.CarrierRepresentation`), series
  versus parallel routes (`PMSubstrate.ProtocolToll`: parallel admittances add), node handoffs per
  round trip, the leptons' on-axis geometry, and whether a protocol has a mass matrix of its own at
  all. Derive the routing histories and rates, their costs, and the tiers each protocol occupies
  (`TierLedger.tiersFor`: up `{0, 2, 3}`, down and lepton `{0, 1, 2}`; `QuarkMasses`,
  `LeptonMasses`); the ledgers still need a cost or selection rule for assigning invariants to tiers.
  Do not fit species parameters to measured masses; derive, then test. Upstream: PMAction, "Size of
  the other wall's detuning".
- **Tier ladder.** `TierLedger` (`Δ⁰…Δ³`, up `{0, 2, 3}`, down and lepton `{0, 1, 2}`) is this folder's:
  where each protocol's three label states land. Derive that placement; PMFlavor's label changes act
  on the label states and do not use the ladder.
- Connect the charged-current operator to the contact vertex in `AmplitudeTrace`. Identify the external carrier states, physical mode weights, and readout normalization.
- Supply the physical tick calibration for `DecayLaw`. Identify the low-energy radiative contribution for elementary widths.
- Determine the physical finite-channel replacement for the muon continuum phase space. For the tau total width, the electronic branching fraction remains an input; hadronic channels depend on [PMHadrons](../PMHadrons/REVIEW-AND-NEXT.md).
- A neutrino-decay prediction requires a physical channel and mass ordering. The corresponding cosmological propagation question is tracked in PMCosmology.
