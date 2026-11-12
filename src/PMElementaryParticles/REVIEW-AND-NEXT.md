# PMElementaryParticles — open work (todo)

Open work on the hadron level (neutron width, kaon and neutral pion, composite states,
phase space and bound-state matrix elements) is in [`PMHadrons/REVIEW-AND-NEXT.md`](../PMHadrons/REVIEW-AND-NEXT.md).

Checked mathematics and the module map are in [`OVERVIEW.md`](OVERVIEW.md). This
file is only what remains, split by what a Lean proof can close (**Part A**) and
what needs a physical model law or measured/selected input (**Part B**). Paper V's elementary-particle library builds clean; run `./build.sh PMElementaryParticles` for current
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

> **Status update:** the measure items (A1, A3–A5) are now optional for the E8 decay
> route.  The finite `BetaLattice`/`LeptonLattice`/`DecayChannel` construction bypasses
> the continuum measure for the E8 rates.  Keep them as comparison/mathematics
> projects, not blockers.

### A1. Two-body phase space from a delta function — done
`PolarMeasure.two_body_from_lebesgue`: the cumulative pair integral over `ℝ³`
(`cumulative_two_body`, from `integral_radial_three`) is `M/(8π)`, and its energy-shell
derivative is `Φ₂ = 1/(8π)`. No supplied step remains.

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

Suggested order (A1 done): **A3**, then **A5**, then **A4** (A4 reuses A1–A3).

## Part B — physical model inputs (not Lean-provable)

### B1 status

**Primary route:** `SubstrateFinalStates` uses the four base protocols from the
16-channel inventory, not SM particle names.  A final state is admissible when
`baseCharge initial = finalCharge final`; `betaMinus_admissible` is the first
example.  SM names below are comparison labels, not the derivation target.

`FinalStateBridge` now supplies a comparison final-state ledger: each channel carries an
initial species, a final species list, and a proof of conserved charge.  The
`ParticleFinalStates` inventory covers μ, τ, π and K channels.  It does not yet
supply the physical matrix element or the full hadronic inventory.  The name-level
bridge to the hadron channel inventory (`ChannelFinalStateLink`, `ParticleChannels`)
is in `PMHadrons`.

`CarrierSpecies` now supplies the channel-label → base-protocol → species bridge
and proves `channelSpecies_charge`: the bridge respects the E8 charge grading.
Base-species masses are assigned (`CarrierSpecies.mass`) and `CarrierCouplings.amplitude` supplies E8 em/weak/strong amplitude slots; `weakCoupling_eq_fermi` connects the weak slot to the W-exchange Fermi coupling.  The carrier
statistics (`PMAction.CarrierStatistics`) and the squared readout (`PMAction.ReadoutRule.born`)
are now derived.  The physical amplitude model remains open.

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
Most of these are now **derived** rather than supplied. The counting measure is
persistence-selected (`ChannelMeasure.probability_uniform_of_const_weight`,
`probability_perm_uniform`); the reduced angular density `1/(32π²)` **factors** as
`(1/4π)·Φ₂` (`PolarMeasure.continuum_angular_density`), with both factors constructed
(`sphere_area_three`, `two_body_phase_space`); the electron measure is
`PolarMeasure.electron_measure_from_integral` (from `massless_lorentz_measure`); and the
spectral modes/weights are the E8 `BetaLattice` template; and the relativistic `2E` normalization
is *derived* (`PolarMeasure.massShell_reduction`: the `δ(p²−s)` mass-shell reduction Jacobian
`2√s`, the same chain-rule shape as A1's `1/2`), so `d³p/((2π)³ 2E)` and the flux `MuonRate.parentFlux
= 1/(2m)` are not separate inputs.  What remains is only the physical readout normalization
(which E8 modes/weights).

### B3 status — done, up to the tick

The per-slot hazard is the six-pillar `Decay.rate` (including the Governor `χ/Δ` and the Toll),
`DecayLaw.rate_eq_pillars`; the exponential law is `ticks_exact` / `ticks_are_survive`; and the
physical lifetime is `tick · (1/rate)` (`DecayLaw.physicalLifetime_eq_tick_mul`). The only input
is the tick `Δ` — the E8 clock period `Δ = 43` (`PMAtoms.E8Tick`) and its SI value (a unit anchor,
`tools/e8p/E8PConstants/PMAtoms/E8TickUnit`).

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

### Lepton / pion / quark mass ledger naming (A7)
`LeptonMasses` and `QuarkMasses` now write every mass purely in the canonical
`E8Values` invariants and decompose it into named tier costs (`muon_ledger`,
`tau_ledger`, and `pionPlus_ledger` now in `PMHadrons.MesonMasses`; `up_ledger` … `top_ledger`), so no bare
measurement literal remains. The muon's vacuum feedback `(χ+σ)α/(1−α)` is
*derived* as the fixed point of its recursive loop (`muonFeedback_fixpoint`), not
fitted. What stays a declared model input (`M`) is the **assignment** of which
invariant pays which tier cost (the paper's proposed protocol ledger): there is no
option family/cost functional over tier ledgers yet.

### Muon lifetime

`MuonLifetime` gives `τ_μ ≈ 2.187×10⁻⁶ s` from E8 `G_F` and `m_μ`, about 0.5%
below the measured value.  The phase space is still the continuum one; the E8
finite-channel replacement remains open.

### Tau

`TauE8` gives the tau lifetime from the E8-input muon lifetime and E8 lepton
masses; `B_e` remains comparison data.  The pion/kaon lifetimes are hadron-level
(`PMHadrons/REVIEW-AND-NEXT.md`).

### B4 status

The hadron channel inventory (`ParticleChannels`, the pion electron mode, and the
blocked tau-hadronic / kaon multibody modes) is in `PMHadrons/REVIEW-AND-NEXT.md`.
B1/B2 (physical final states and measure normalization), A5, and A4 remain
model/analysis inputs.

### B5 status — interface complete

`RadiativeCorrection` is the supplied-`R` interface (`correctedRate` / `correctedLifetime`), and
the hadronic matrix elements are the `PMHadrons.BoundStateOverlap` / `PMHadrons.Emission` overlap
construction (`emissionWidth` = Toll boundary × overlap² × phase space). The short-distance
radiative factor is derived: its one-loop coefficient `(3/4π)(1+2Q̄)` comes from
`PMAction.ContactRunning` (Fierz in `ContactFierz`, loop weight in `LoopMeasure`) and gives
`PMHadrons.ShortDistanceRunning.runningFactor_from_contact`. The low-energy radiative part and
the bound-state values remain supplied inputs (`M`).

### B5. Absolute coupling and corrections
Radiative corrections, hadronic final states, bound-state matrix elements, and an
absolute coupling/lifetime prediction remain inputs. The tau lifetime uses the
measured muon lifetime and branching fraction; the neutron rescaling is a
conditional arithmetic identity. The hadronic matrix elements now have a concrete
home: `PMHadrons.BoundStateOverlap` (the overlap) and `PMHadrons.Emission`
(`emissionWidth` = Toll boundary × overlap² × phase space).

## Scope of the fifth-power result
`MuonRate.muon_rate`'s `m⁵` is a consequence of the specified four-dimensional
contact interaction, state normalization and massless/fixed-ratio phase-space model
at fixed dimensionless couplings — not a universal rule for every persistent
excitation (`SubstrateBridge` contains distinct cubic and quintic laws). The
remaining work is to select the physical law, not to hide its hypotheses.

## Verification

Run `./build.sh PMElementaryParticles`. No Paper VI imports; permitted axioms `propext`, `Classical.choice`, `Quot.sound`.


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


### Five-task sweep

Completed structural follow-ups at this level:

```
TopTransition          top → bottom + charged vector, charge + structural rate
NeutrinoPropagation    two-flavour phase, survival/transition, bounds
```

The composite / bound-state follow-ups (`BoundStateOverlap`, `CompositeBinding`,
`MultiBodyPhaseSpace`) are in `PMHadrons`.
