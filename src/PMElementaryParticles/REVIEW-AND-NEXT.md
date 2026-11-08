# PMElementaryParticles — open work (todo)

Checked mathematics and the module map are in [`OVERVIEW.md`](OVERVIEW.md). This
file is only what remains, split by what a Lean proof can close (**Part A**) and
what needs a physical model law or measured/selected input (**Part B**). Paper V's elementary-particle library builds clean; run `./check.sh` for current
counts. The sibling `PMAtoms` library has its own `REVIEW-AND-NEXT.md`.

## How to test the draft paper

The paper's checkable content decomposes into four layers: (1) the **stipulated
protocol inventory** (16 channels, four base protocols, sterile vacancy) — now
formalized in `ProtocolInventory`, with `SubstrateLedger.substrate_has_components`
showing the substrate actually contains each component (chirality, colour,
charge, protocols, sterile vacancy, tier ladder); (2) the
**routing dynamics** (allowed transitions, latency descent, terminal states) —
the generic `Routing` model, the concrete charge-conserving `Decay` relation
(`ProtocolDynamics`), and the paper's routing caveats (`ProtocolCaveats`:
lower latency need not be reachable; routing does not force stability) exist; the
*specific* allowed routes and rates remain inputs; (3) the **quantitative
rates** (`MuonRate`, `MassiveWidth`, `InclusiveMixing`, `TauLifetime`) — done,
modulo the measure gaps in Part A; (4) the **physical identifications**
(pillars→spin/colour/charge, neutrino duality, CPT, particle ledger, physical
interaction/measure) — model inputs, in Part B. So the remaining *protocol* work is
layer 2 plus tiers; the remaining *decay* work is Part A's measure construction.

## Part A — mathematical gaps fillable in Lean

These are analysis/probability tasks: the physics input is the standard
Lorentz-invariant measure, and the goal is to **construct** it rather than supply
its value. Each names the current placeholder to replace.

> **Status update:** A1–A3 are now optional for the E8 decay route.  The finite
> `BetaLattice`/`LeptonLattice`/`DecayChannel` construction bypasses the
> continuum measure for the E8 rates.  Keep A1–A3 as comparison/mathematics
> projects, not blockers.

### A1. Two-body phase space from a delta function
`MuonRate.two_body` currently proves only the arithmetic
`4π/(2π)²·(1/4)·(1/2) = 1/(8π)`; it does **not** construct a measure. Target:
build the massless two-body integral
`Φ₂ = ∫ d³k/((2π)³ 2E_k) · d³k̄/((2π)³ 2E_k̄) · (2π)⁴ δ⁴(q − k − k̄)`
and **compute** `Φ₂ = 1/(8π)` from it, then re-derive `pair_coeffs`
(`A = 1/(96π)`, `B = 2A`). Note Mathlib's `integral_dirac` handles point masses,
not a surface delta, so this likely needs an energy-shell/fiber (coarea)
construction plus `MeasureTheory` change of variables. **Started:** `PhaseSpace.solidAngle_one` derives the `4π` angular weight from the
iterated direction integral over `(z,φ)`, `average_one` normalizes it, and
`electron_measure_radial` records the massless radial measure. Remaining: the
energy-shell **delta** reduction and the full two-body measure. This is the "not a
constructed delta-function measure" gap.

### A2. Radial energy-shell reduction of the electron measure
`MuonRate.electron_measure` is an algebraic identity. Target: derive
`4π E²/((2π)³ 2E) = E/(4π²)` from `∫_{ℝ³} d³p` in spherical coordinates (surface
measure of `S²` times `p² dp`, `p = √(E²−m²)`), for the massless case first, then
the massive one. **Status:** the angular area `4π` (`PhaseSpace.solidAngle_one`), the massless radial
identity (`PhaseSpace.electron_measure_radial`) and the massive radial Jacobian
(`MassiveDaughterSpectrum.radial_measure`) are proved. Only the global `∫_{ℝ³}`
spherical change of variables remains, and Mathlib has **no** spherical-coordinate
integral, so this item is blocked on that infrastructure rather than on our work.

### A3. Three-body phase-space factorization
The three-body measure is used but not factored. Target: factor it into
(pair invariant mass) × (pair angular measure) × (spectator energy), and derive the
`MassiveDaughterSpectrum` density `pair_density` as a *consequence* rather than an
input. This is the concrete mathematical content of former review item 2.
Depends on A1–A2.

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

Suggested order: **A1 → A2 → A3**, then **A5**, then **A4** (A4 reuses A1–A3).

## Part B — physical model inputs (not Lean-provable)

### B1 status

**Primary route:** `SubstrateFinalStates` uses the four base protocols from the
16-channel inventory, not SM particle names.  A final state is admissible when
`baseCharge initial = finalCharge final`; `betaMinus_admissible` is the first
example.  SM names below are comparison labels, not the derivation target.

`FinalStateBridge` now supplies a comparison final-state ledger: each channel carries an
initial species, a final species list, and a proof of conserved charge.  The
`ParticleFinalStates` inventory covers μ, τ, π and K channels, and
`ChannelFinalStateLink` matches their names to `ParticleChannels`
(`muon_names`, `tau_first_name`, `pion_names`, `kaon_prefix`).  It does not yet
supply the physical matrix element or the full hadronic inventory.

`CarrierSpecies` now supplies the channel-label → base-protocol → species bridge
and proves `channelSpecies_charge`: the bridge respects the E8 charge grading.
Base-species masses are assigned (`CarrierSpecies.mass`) and `CarrierCouplings.amplitude` supplies E8 em/weak/strong amplitude slots; `weakCoupling_eq_fermi` connects the weak slot to the W-exchange Fermi coupling.  The physical amplitude model remains open.

### B1. Physical interaction and final states
Connect the substrate update / reference / charged-current operators to the contact
vertex used in `AmplitudeTrace`, and state which carrier transitions give the
external one-particle states and decay channels. Paper II supplies conditional
operator bridges; the identification and normalization need a model law.

### B2 status

`PersistenceMechanics.ChannelMeasure` supplies the finite normalized measure, and
`PMAtoms.SpectralMeasure.betaChannelMeasure` instantiates it with the beta
spectral weights.  The remaining input is the physical mode selection/normalization.

### B2. Select the measure and normalizations from the substrate
Independently of A1–A2 (which construct the *standard* measure), the **choice** of
counting measure, reduced angular density `1/(32π²)`, electron measure, parent flux
`1/(2m)` and overall normalization must be derived from the selected physical
readout — they are currently supplied.

### B3 status

Structurally solved: `DecayChannel.lifetime = 1/rate`, `physicalLifetime` carries
the tick conversion, and the persistence hazard layer gives exponential survival.
The missing input is the numerical E8 tick.

### B3. Decay law from the chosen dynamics
Specify subsystem, environment/readout and the controlled approximation giving
constant hazard; relate the width to `Γ = width/ħ` and the physical tick. `DecayLaw`
proves the consequences of a supplied per-tick cost; persistence alone does not
force a nonzero hazard or an exact exponential.

### B4. Particle protocols, routing dynamics and mass ledger
The channel inventory/counting is checked (`ProtocolInventory`: 16 channels, four
base protocols, sterile vacancy, charges). Now proved in `ProtocolDynamics`: charge-conserving decay `Decay`, finite descent
(`no_infinite_chain`), tier-0 terminality, and the muon `e+ν+ν̄` example; tier labels are
`Tier = Fin 4`: a point (`Δ⁰`), then 1D (`Δ¹`), 2D (`Δ²`), 3D (`Δ³`). Each protocol's
mass ledger occupies a subset (leptons/down 0,1,2; up-type 0,2,3). The draft's
"three generations" prose was corrected to this "point then 1,2,3 dimensions"
phrasing in `4_protocols.tex`; no tier beyond the volume (`Δ⁴`) exists. What remains
is only the per-protocol tier subset, which is a ledger input. Still open: the **specific** allowed routes and their rates (model
inputs), which routing histories represent the particles, their resource costs,
and why the mass ledger is selected. Charge/
conservation/mass checks are constraints, not a selection. The muon/tau mass formulas are recorded as ≈2.4σ and
≈2.1σ tensions; the factor-six contextual neutrino prescription is excluded. Do not
promote a numerical fit or a symmetry-class count to a particle classification.

### Neutron width
The massless-pair diagnostic is superseded by `NeutronRate`, which uses the
massive-electron phase space

```
f = ∫_{1}^{m_n−m_p} E√(E²−1)(m_n−m_p−E)² dE
```

and the E8 axial assignment `g_A = σ/D = 5/4`.  The width is

```
Γ = G_F²|Vud|²/(2π³)·(1+3g_A²)·f.
```

With `f ≈ 1.636`, `Vud² ≈ 0.949`, this gives `τ ≈ 9.8×10² s`, about 11% above
the measured `8.78×10² s`.  The recoil-corrected endpoint
`E_rec = (m_n² + 1 − m_p²)/(2m_n)` gives `f ≈ 1.630` and `τ ≈ 9.8×10² s`; a
supplied `4%` radiative factor brings it to `≈9.4×10² s`.  The residual few
percent is the remaining strong/electroweak correction, not a free fit.  The
full angular Dalitz density and a derived radiative correction are still open.
The environmental `beamLifetime = (215/213)·neutronLifetime` is formalized as a
conditional rescaling.

### Muon lifetime

`MuonLifetime` gives `τ_μ ≈ 2.187×10⁻⁶ s` from E8 `G_F` and `m_μ`, about 0.5%
below the measured value.  The phase space is still the continuum one; the E8
finite-channel replacement remains open.

### Tau and pion

`TauE8` gives the tau lifetime from the E8-input muon lifetime and E8 lepton
masses; `B_e` remains comparison data.  `PionWidth` now uses `fπ = v/(Δ²+Δ−χ) = v/1890`; the resulting lifetime is
`≈2.52×10⁻⁸ s`, about 3% below the measured `2.60×10⁻⁸ s`.

### Kaon and neutral pion

`KaonWidth` now uses `fK = v/(Δ²−ν²) = v/1593` and `|Vus| = s₁₂c₂₃`; the
partial `K⁺ → μ⁺ν` lifetime is about `2.0×10⁻⁸ s` versus `1.95×10⁻⁸ s`.
`NeutralPionWidth` uses `fπ` and the identical-photon factor `32` in the
`130 MeV` convention (the earlier `128` was a factor-four error), giving
`τ(π⁰) ≈ 8.46×10⁻¹⁷ s` versus `8.52×10⁻¹⁷ s`.

### B4 status

`ParticleChannels` now has concrete μ, τ, π, and K inventories with provenance
labels (`e8`, `calibrated`, `modelInput`, `blocked`).  The pion electron mode has an E8 rate (`pionElectronWidthE8`).  The tau hadronic
channels and kaon multibody modes are inventoried but blocked on hadronic matrix
elements.  B1/B2 (physical final states and measure normalization), A5, and A4
remain model/analysis inputs.

### B5 status

`RadiativeCorrection` provides the supplied-`R` interface; the actual radiative
factors remain open.

### B5. Absolute coupling and corrections
Radiative corrections, hadronic final states, bound-state matrix elements, and an
absolute coupling/lifetime prediction remain inputs. The tau lifetime uses the
measured muon lifetime and branching fraction; the neutron rescaling is a
conditional arithmetic identity.

## Scope of the fifth-power result
`MuonRate.muon_rate`'s `m⁵` is a consequence of the specified four-dimensional
contact interaction, state normalization and massless/fixed-ratio phase-space model
at fixed dimensionless couplings — not a universal rule for every persistent
excitation (`SubstrateBridge` contains distinct cubic and quintic laws). The
remaining work is to select the physical law, not to hide its hypotheses.

## Verification

Run `./check.sh`. No Paper VI imports; permitted axioms `propext`, `Classical.choice`, `Quot.sound`.


### Channel → particle join

`ChannelParticleLedger` now supplies one row per substrate channel:

```
channel, index, base protocol, species, colour, chirality, anchor, charge
```

with `ledger_length = 16`, `active_channels_card = 15`, and
`channelCharge_eq_Q` tying the rational charge to `ChargeProtocols.Q`.  The 15
active channels are not 15 independent particles: they are colour/chirality
copies of the four base protocols.  Generational tiers remain a separate ledger.


### Tier and status ledgers

`TierLedger` fixes the tier subsets: up-type `{0,2,3}`, down/electron/neutrino
`{0,1,2}`, and assigns `massProvenance`/`decayProvenance` labels
(`e8`, `comparison`, `partialE8`, `blocked`, `notModeled`, `stable`).
`ChannelStatusLedger` expands every active channel row over its allowed tiers,
recording the mass and decay provenance per row.  These are status ledgers, not
new derivations.


### General substrate transition form

`SubstrateTransition` supplies the general decay form:

```
partialWidth i f = |⟨f|T|i⟩|² · phaseSpace i f
totalWidth i     = Σ_f partialWidth i f
lifetime i       = 1 / totalWidth i
branching i f    = partialWidth i f / totalWidth i
```

`singleChannel` is the one-cohort instance; the muon E8 width is proved to be
such an instance (`muonSystemE8_totalWidth`).  The operator and phase-space
entries remain supplied inputs; hadronic matrix elements are still open.


### Carrier-product operator

`CarrierTransitionOperator` supplies a first substrate-native operator:

```
T(i,f) = weak(source) · Π_{x∈f} weak(x)   when Decay i f,
       = 0                                  otherwise.
```

`muonOperatorSystem` and `tauOperatorSystem` instantiate the general form with this
`T`; their total widths are `|T|²·phase`.  This removes the per-particle amplitude
from the muon/tau leptonic examples.  It is a leading carrier-product operator,
not the full nonperturbative interaction; charged pion/kaon matrix elements still
need composite states.


### Composite states and transition

`CompositeStates` adds signed constituent cohorts: `pionPlus`, `pionZero`,
`kaonPlus`, `proton`, `neutron`, with charges proved from the base-protocol
charges.  `CompositeTransition` extends the carrier-product operator to composite
cohorts and proves `K⁺ → π⁺ π⁰` charge conservation and its operator entry.  These
are structural/comparison states, not a derivation of the bound-state spectrum.


### Composite phase space and rate

`CompositePhaseSpace` adds the standard two-body phase space

```
Φ₂ = √((M² − (m1+m2)²)(M² − (m1−m2)²)) / (8πM²)
```

and the structural rate `compositePartialWidth = |T|²·Φ₂`.  The `K⁺ → π⁺ π⁰`
instance uses the E8 composite masses; `kaonPionPhase_pos` proves it is above
threshold and `kaonPionRate_nonneg` proves the structural rate is nonnegative.
The hadronic matrix element is still the carrier-product operator, not a full
bound-state calculation.


### Bound-state matrix element

`HadronicMatrixElement` makes the nonperturbative object explicit:

```
⟨π⁺π⁰|T|K⁺⟩
```

`BoundStateMatrixElement.value` is a supplied complex input; `kaonPionRate` proves
the rate consequence `|value|²·Φ₂` and its nonnegativity.  The value is **not**
derived here.  This is a deliberate interface, not a fake calculation.


### Five-task sweep

Completed structural versions of the five follow-ups:

```
BoundStateOverlap      overlap as a finite inner product (wavefunction supplied)
CompositeBinding       mass = constituent mass − binding (binding supplied)
MultiBodyPhaseSpace    massless three-body Φ₃ and rate form
TopTransition          top → bottom + charged vector, charge + structural rate
NeutrinoPropagation    two-flavour phase, survival/transition, bounds
```

The first two remain genuine model inputs: no bound-state wavefunction or binding
energy is derived.  The last three are concrete structural additions.
