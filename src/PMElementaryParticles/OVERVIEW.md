# PMElementaryParticles — overview of checked results

Why continuum phase space is correct on a lattice substrate, and when it is not: [`CONTINUOUS.md`](CONTINUOUS.md).

The single map of what Paper V proves and what later work can reuse. Open work is
in [`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md); build instructions are in
[`README.md`](README.md). Sources are under `PMElementaryParticles/`, imported by `PMElementaryParticles.lean`.
Theorem names are entry points, not exhaustive lists; the Lean source is ground
truth. Library order: PMSubstrate → PMAction → PMConstants → PMElementaryParticles → PMFlavor → PMHadrons → PMAtoms → PMCosmology (`AuditDependencies`). This folder imports nothing from PMFlavor.

## Scope

`RefreshMap.minimal` and `occupied_count` show that retaining the base protocol and active flag gives the coarsest deterministic description of weak refresh that preserves the inventory readout. Eight classes occur, including the vacancy. Colour permutations preserve each class and two refreshes restore each channel. At a canonical hypercharge maintenance visit, the addressed payload row exchanges its live discrepancy with its incoming record (`payload_visit`). Equality of next live bits for every incoming record array is equivalent to equality of channel addresses (`same_payload_readout_iff`). Even two active bulk channels of the same protocol can be distinguished this way (`routing_misses_payload`). With ledger arrays transported together, initially clean records and one designated channel marked in the incoming live array, `marked_payload_return` gives clean outputs through visit N on an orbit of least period N. At visit N+1 only the marked address reads true. On a nonreturning orbit `marked_payload_open` gives clean outputs at every positive visit.

For the candidate that consults a fixed bit array at the incoming address and applies one weak flip on true, `feedback_changes_iff` identifies the changed protocol labels. `feedback_injective_iff` proves that reversibility on channel labels requires and suffices for equality of the bits on each weak pair. A single active mark produces a collision (`single_active_collision`). For one addressed maintenance swap followed by routing on the returned live bit, clear incoming live payloads suffice to recover the incoming channel and entire ledger (`recover_visit_channel`, `visitRoute_clean_injective`). The record bits may be occupied. On unrestricted inputs even the complete outgoing ledger can coincide for two weak partners (`visitRoute_collision`). For consecutive visits without intervening transport, `pairVisit_exact` projects a moving channel onto its weak pair. Starting with clear live bits, the fifth pair state equals the first. At any known visit count the pair state identifies the initial position and both initial record bits (`pair_clean_recover`). A fixed channel restores its entire ledger after two visits (`fixed_visit_twice`).

The Map's clean requirement is exact. Recovery after one visit needs only the partner row's live bit clear (`recover_partner_clean`), so the visit with routing is reversible on every input whose eight active payload rows are clear, with static rows unrestricted (`visitRoute_active_clean_injective`); one occupied active row already gives a collision (`visitRoute_collision`). A gate that reads different bits on two weak partners collides them on the channel, so any reversible extension must export a record separating the partners, that is, the doublet position (`asymmetric_gate_records`). The weak flip moves exactly the active channels (`moves_iff_active`).

`CoherentGate` is the coherent version on one weak pair. Gating the two partners at angles `a` and `b` gives output columns with overlap `sin (a − b)` (`cross`), so the gate is reversible exactly when the angles agree up to a half turn (`columns_orthogonal_iff`). With records written beside the outputs the overlap is `sin (a − b) · ⟨r₀, r₁⟩` (`recorded_orthogonal_iff`): any unequal angles, however close, need exactly orthogonal records, one full bit of doublet position per event (`unequal_needs_orthogonal`).

**Protocols are not wire modes (2026-11).** The odd carrier modes of a class are the wire's Dirac components, four axes × two walls (`PMAction.CarrierVacuumSector`), and colour cannot act on them while commuting with `β` and the `αⱼ` (`PMAction.ColourRegister`). So protocol identity (lepton or quark, colour, weak partner) is a separate register; the 16-carrier packet is its count and gauge actions. Earlier readings that put the lepton pair on axis `0` and the up/down pair of colour `i` on axis `i` of the wire are withdrawn: `BetaReference` and `UpDownWire` (modules removed), `DoubletSign`'s wire-mode count, `ProtocolReadout`'s carrier-state reading, `CycleReadout`'s weak-pair reading, and the reference-hold test (module removed). Their theorems remain as carrier and matrix facts; the partner difference has to come from the protocol register.


**Protocol readout (numerical, `tools/protocol_readout_scan.py`).** On the derived wire (`PMAction.ReferenceClassHop`: reference wall `κ_R = (K, k, k)`; `PMAction.CarrierAdmittance`: other wall class-blind, `κ_O = (K, K, K)`; `K = 1`) the cycle resonance is `δ³ = −1` (`PMAction.OtherWallStationary`). At every cube root the bare wire has `m₁ = 0` and `m₂/m₃ = √(3/2) k`: `0.0045` for `k = α/2`, `0.0089` for `k = α`, the same for every protocol. The data (`m_μ/m_τ = 0.0595`, `m_s/m_b ≈ 0.019–0.022`, `m_c/m_t ≈ 0.0036–0.0042`) then need a weight `s` on the heavy label (both walls) per protocol: `s_e : s_d : s_u ≈ 1 : 2.7–3.2 : 12–13.5` for `α/2` (`1 : 2.6–3.1 : 9.6–10.6` for `α`), ordered by charge; the heavy label's mass scales as `s²`. The lazy flip law squares the bare ratio (`2·10⁻⁵`), far below every protocol, so the data favour the coherent event. Earlier numbers on the withdrawn wire (`K = 1`, `k = α/2` on both walls by the axis rule): `m₂/m₃ ≈ k^{2/3} = 0.023`, weights `w_e : w_d : w_u ≈ 1 : 3 : 16–18`, `|V_us| ≈ 0.002` (same root) or `0.26`, `|V_cb| ≈ 0.17`, `|V_ub| ≈ 0.027` (different roots). CKM on the derived wire (weights as fitted): same root `|V_us| ≈ 0.0001`, `|V_cb| ≈ 0.009`, `|V_ub| ≈ 0.008`; different roots `|V_us| = √3/2 ≈ 0.866`, `|V_cb| ≈ 0.010`, `|V_ub| ≈ 0.011` (data `0.225`, `0.041`, `0.0037`): the bare wire's rotation is not the CKM. Mixing tests on the derived wire (`tools/mixing_candidates_check.py`, masses held at data): `|V_us| = 0.225` is reached by a relative flip phase, a light-class asymmetry, or an other-wall cycle phase or asymmetry, so it does not discriminate; `|V_cb|` stays at `0.002–0.010` under every deformation tried (those, the weight on one or both walls, a joint fit, `k/K` from `α/4` to `10α`), with `|V_cb| ≈ |V_ub|`. So the wire's mass matrices cannot give `|V_cb|`; PMFlavor's transfer readout does (`PMFlavor.ReferenceRouting`). Charge-weight test: one `a` in `s ∝ e^{a Y_R}` gives down and up `0.82` and `0.77` (PDG mixed scales), `0.74` and `0.75` (`m_b`, `m_t` at their own scale), 2–11% apart across quark-mass choices (`k = α/2`; `7–18%` at `k = α`). Lightest masses: a real offset `δ = −1 + ε` off the resonance reproduces each `m₁/m₂` with `ε ≈ 0.038 (e), 0.14 (d), 0.0024 (u)`, keeping `m₂/m₃` within 2–7%; with those offsets the same-root CKM is `|V_us| ≈ 0.063`, `|V_cb| ≈ 0.007`, `|V_ub| ≈ 0.0065`.

`streamRoute` tests a different coupling: the common ledger stream advances independently and its new live bit controls the channel after each tick. Clean payload readouts preserve every channel (`streamRoute_clean`). With the single-address preparation on an orbit of least period N, the complete route at tick N+1 equals the single-address gate (`streamRoute_first_return`). An active mark therefore merges two routes with identical outgoing streams.

With inventory channels carried as configuration values, the native port update exports the entering channel exactly. `native_route_iff` characterizes when it realizes a proposed conditional weak route: the incoming record must already contain the target. `native_outputs_distinct` separates distinct incoming labels on the outgoing record. A single common target fails across the inventory (`no_common_target`). The repair root preserves doublet position on its vector-carrier addresses (`repair_root_preserves_position`). A table supplying literal targets needs at least twelve slots, one per weak orbit (`target_table_bound`). On a connected stationary native background even arbitrary site and port selection gives only two port values (`stationary_source_insufficient`). An orbit index and one position bit identify each channel; feedback preserves the orbit and toggles that bit exactly on a marked active channel (`feedback_position`).

`RefreshMap.gated_word_matches` identifies the conditional weak toggle on all channels with the antipodal carrier Weyl word on the active bank and identity on the static bank. If a common clock mask-change bit gates that word, `clockRoute_endpoints` reduces the entire route to the initial and final mask values; `clockRoute_closes` restores every input channel over a full clock cycle. This coupling uses a supplied mask and word-level gate.

Hadron-level modules (composite masses, composite states and transitions, pion/kaon/neutron
widths, the particle channel inventory) live in [`PMHadrons`](../PMHadrons/OVERVIEW.md).
Downstream libraries import `PMElementaryParticles.Values` (like `PMSubstrate.E8Values`,
`PMConstants.Values`, `PMFlavor.Values`): `me`, `hbarc`, `electronTime` (+ `electronTime_tight`),
`αe`, `αinv`, `fermiME` (+ `fermiME_tight`), `muon`, `tau`, the six quark masses and the muon/tau
lifetimes in seconds, with their bounds. Prove a bound there once rather than inline.

Shared units and couplings used by every level are in `SharedUnits` (`me`, `ħc`, `α`, `α⁻¹`,
their bounds, and `G_F` in `m_e⁻²`).


Paper V models **elementary-particle protocols and their decay** on the E8
substrate. It supplies: the V−A contact amplitude and its `W`-exchange origin, the
muon and massive-daughter decay widths, the pair/phase-space tensor machinery, the
decay-law relation to Paper I survival, and the particle/mass/charge protocol
checks against data (recorded as tensions, not fits). It does **not** select the
physical interaction, the phase-space normalization, the absolute coupling, or the
particle ledger; those remain model inputs.

## Selected E8 decay checks

Frozen comparison values live outside the theorem tree.  The elementary-particle
(electron/muon/tau) checks are:

| decay | E8 model | comparison | status |
|---|---:|---:|---|
| μ → e ν ν̄ | 2.187×10⁻⁶ s | 2.197×10⁻⁶ s | E8 inputs, continuum phase space |
| τ → e ν ν̄ | ≈2.9×10⁻¹³ s | 2.90×10⁻¹³ s | E8 masses + supplied `B_e` |

The nucleon and meson decay checks (n, π, K, π⁰) are hadron-level and live in
[`PMHadrons/OVERVIEW.md`](../PMHadrons/OVERVIEW.md).

The structural channel/status ledgers are in `ChannelParticleLedger`,
`TierLedger` and `ChannelStatusLedger`.  SM particle names in the comparison
ledgers are labels; the substrate objects are protocols, tiers and cohorts.

## Amplitude, rate and width

| Modules | Checked result | Retained inputs |
| --- | --- | --- |
| `SpinorRateBridge` | Paper II's actual bilinear amplitude in Paper V's real-momentum convention: initial-spin-averaged square `64 G²(p·k̄)(p_e·k)` | V−A vertex, on-shell states, complete orthonormal kernel bases |
| `MuonAmplitude`, `MassiveMuon` | V−A trace algebra; the muon's mass cancels between chiral vertices (`chiral_sandwich`, `massive_trace`, `massive_amplitude`) | — |
| `MassiveExternalAmplitude` | Same `64 G²(p·k̄)(p_e·k)` for **arbitrary real masses** on all four legs (`spin_averaged`, `rate_input`) | Contact vertex, signed antiparticle convention |
| `WExchangeRate` | Contact amplitude as the `q→0` limit of tree `W` exchange; `G=√2g²/(8m_W²)`, `G=1/(√2v²)` (`exchange_rate_input`, `exchange_rate_fermi`, `bases_exist`) | That this exchange is the substrate interaction |
| `WeakMatching` | Mediator matching `M_W²=g²v²/4`, `G=1/(√2v²)`, normalized spectrum | Physical coupling/mediator |
| `TauE8` | `tauLifetimeE8 = τ_μ(m_μ/m_τ)^5 B_e`, positivity | supplied `B_e` |
| `CarrierCouplings` | `CarrierAmplitude`, `amplitude`, `CarrierTransition`, E8 `em/weak/strong` slots, `CarrierTransition.amplitude`, `carrierMatrixElement` (actual external-spinor contact amplitude), `CarrierExternalStates` / `matrixElement`, `CarrierSpinorState`, `OnShellExternalStates`, `OnShellExternalStates.matrixElement`, transition weight, `weakCoupling_eq_fermi` | amplitude model selection |
| `TierLedger` | `tiersFor` up `{0,2,3}` / down/lepton `{0,1,2}`, `massProvenance`, `decayProvenance`; tier subsets and provenance labels. |
| `TopTransition` | `Boson`, `topInitial`, `bottomFinal`, `topFinal`, `topT`, `topRate`, charge conservation. |
| `NeutrinoPropagation` | `TwoFlavour`, `phase`, `survival`, `transition`, bounds and sum rule. |
| `CarrierTransitionOperator` | `weakOf`, `carrierProductAmplitude`, `substrateOperator`, `substrateOperator_zero_of_not_decay`; muon/tau operator systems with `totalWidth = |T|²·phase`. |
| `SubstrateTransition` | general transition form `partialWidth = |⟨f|T|i⟩|²·Φ`, `totalWidth`, `lifetime`, `branching`; `singleChannel`; muon E8 width as an instance. |
| `ChannelStatusLedger` | `ChannelStatusRow`, `statusRowsFor`, `statusLedger`; channel × allowed-tier expansion with mass and decay provenance. |
| `ChannelParticleLedger` | `ChannelRow` (channel, index, base protocol, species, colour, chirality, anchor, charge), full 16-row `ledger`; `ledger_length`, `active_channels_card = 15`, `channelCharge_eq_Q`, `species_none_iff_sterile`. |
| `SubstrateFinalStates` | substrate-native `BaseProtocol` final states, `baseCharge`, `AdmissibleFinalState`, `betaMinus_admissible`; primary B1 ledger before SM comparison labels. |
| `FinalStateBridge` | `FinalStateChannel` with conserved `chargeSum`; `betaMinus`, `neutrinoFinal`, `finalState_charge_conserved`; first B1 final-state ledger. |
| `CarrierSpecies` | `CarrierSpecies`, `ofBaseProtocol`, `channelSpecies`, `CarrierSpecies.charge`, `channelSpecies_charge`, sterile/no-species lemmas; channel label → base protocol → species | mass/amplitude assignment |
| `RadiativeCorrection` | supplied `R`, `correctedRate`, `correctedLifetime`, positivity | derived radiative correction |
| `MuonLifetime` | E8-input muon width `G_F²m_μ⁵/(192π³)`, `muonLifetime`, positivity; `muonWidth_eq_integral` | finite spectral-channel phase space |
| `MuonRate` | `192π³` derived: `pair_kinematics`, `tensor_coeffs`, `two_body`, `electron_measure`, `rate_density`, `muon_rate = G_F²m⁵/(192π³)`, `spectrum_form` | `Φ₂=1/(8π)` and the electron measure/flux derived in `PolarMeasure` |
| `PolarMeasure` | the `ℝ³` momentum measure by spherical change of variables: `sphere_area_three`, `integral_radial_three`, `massless_lorentz_measure`, `two_body_phase_space`, `massShell_reduction`; `two_body_from_lebesgue` (`Φ₂ = 1/(8π)` as the energy-shell derivative of the cumulative pair integral over `ℝ³`) | — |
| `MassiveDaughterSpectrum` | Massive charged daughter, massless neutrino pair: `threshold`, `kinematics`, `radial_measure`, `pair_density`, `massless`, `rate_positive`, `width_scaling` | Contact vertex, transported pair average |
| `MassiveWidth` | Closed massive-daughter width `G²m⁵/(192π³)·[1−8r+8r³−r⁴−12r² log r]`; `closed_width`, `phase_zero/one/continuous`, `phase_positive`, `threshold_width` | Tree contact spectrum, normalizations |
| `MuonLifetimeCorrected` | `τ_μ = τ_tree/(f(r)·q)`: `r = (m_e/m_μ)²` (`r_bounds`), derived phase factor `f(r) = MassiveWidth.phase r` (`phase_bounds`, `0.99981295`), `α = 1/geometricIndex`, `corrected_bounds` `2.196987–2.196998 µs` (measured `2.1969811(22)`); e8p `muon_lifetime_s` | one-loop QED factor `q = 1 − (α/2π)(π² − 25/4)` (Kinoshita–Sirlin), supplied; higher orders (≈5 ppm) not included |
| `InclusiveMixing` | Unresolved orthogonal channels: `amplitude_weight`, `equal_kinematics` (sum = 1 for any unitary mixing; applied to the on-axis matrix in `PMFlavor.InclusiveWidth`), `kinematic_bounds` | Orthogonal final states, common kinematics |

## Pair tensor and continuum angular integral

| Modules | Checked result | Retained inputs |
| --- | --- | --- |
| `PairIsotropy` | Rest-frame pair moments from sign flips / axis swaps / unit length: vanishing first and off-diagonal moments, diagonal `Φ/3`; `rest_covariant`, `normalized_rest` | Volume `1/(8π)` |
| `PairTransport` | Concrete `axisAverage`; Lorentz transport `transported_tensor`, `frame_independent`; `boost_lorentz`, `boost_to`, `timelike_pair`; `muon_density`, `axis_muon_density` | `Φ=1/(8π)`, electron measure, flux |
| `ContinuumPair` | Iterated Lebesgue angular integral with reduced density `1/(32π²)`: `volume=1/(8π)`, `first_moment`, `second_moment`, linearity on continuous test functions, `pair_massless`, `pair_contraction`, `massive_density`; invariance under rotations about the polar axis (`average_rotate_polar`, any `f` periodic in `φ`) and under `z ↦ −z` (`average_reflect_polar`) | Angular parametrization/density specified, not substrate-derived |
| `MassivePair` | Rest-frame tensor of a pair with masses `m₁`, `m₂` from the angular symmetries (`massive_rest_tensor`), covariant form `Q²⟨k₁k₂⟩ = Φ(P²/3) g Q² + Φ(E₁E₂ − P²/3) q q` (`massive_rest_covariant`), `massless_limit`, `two_body_kinematics`, `shells` | — |
| `ElectronMeasure` | Massive daughter measure from `∫_{ℝ³}`: `∫ g(E) d³p/((2π)³2E) = (1/4π²)∫_μ^B √(E²−μ²) g(E) dE` (`massive_lorentz_measure`); the massive width is the Lebesgue integral of the flux-weighted pair part over the daughter momentum (`width_from_lebesgue`) | three-body factorization into daughter × pair, flux `1/(2m)` |
| `NullBoost` | Boost along an axis acting on a massless leg: `|k'| = γ(|k| + βk₀)` (`nrm_boost`), inverse (`boost_inv`), Jacobian `|k'|/|k|` (`det_J`, `boost_hasFDerivAt`); `d³k/|k|` is boost invariant (`measure_invariant`) and so is the two-leg measure as an iterated integral (`pair_invariant`) | — |
| `TauBranching` | `B(τ→eνν̄) = 1/(1 + f(r) + N_c h)`: leptonic ratio from the derived phase factor at the E8 masses (`phase_bounds`, `0.9724–0.9727`), `N_c = D − 1 = 3` (`colours_eq`); parton level `h = 1` gives `0.2010–0.2012` (`parton_level`); the supplied `0.1782` needs `h = 1.2129–1.2132` (`supplied_needs`) | hadronic factor `h` (PMHadrons) |
| `PairShell` | Shell coordinates `(E, ν, φ)` for a massless pair at total momentum `b e₀`: `|k| = (E + b cos ν)/2`, `|k̄| = (E − b cos ν)/2` (`nrm_Ψ`, `nrm_Ψ_bar`), Jacobian `(sin ν/8)(E² − b² cos²ν)` (`det_J`, `Ψ_hasFDerivAt`), injective (`Ψ_injOn`), onto off a null half-plane (`Ψ_onto`, `image_ae_univ`); `∫ g d³k/(|k||P⃗−k|) = ∫_S (sin ν/2) g∘Ψ` for every `g` (`shell_integral`) | — |
| `PairSphere` | The pair tensor over the shell, computed: solid-angle moments `4π`, `0`, `(4π/3)δᵢⱼ` (`separable`, `mono_avg`); rest tensor `4π/12 g Q² + 4π/6 q q` (`rest_covariant`) and its boost by any Lorentz `Λ` (`transported`); the shell legs are the rest pair boosted to `q = (E, b, 0, 0)` (`leg_spatial`, `shellBoost_legs`, `shellBoost_rest`); `∫ k^μ k̄^ν dΩ*/(32π²) = Φ/12 g q² + Φ/6 q q`, `Φ = 1/(8π)` (`shell_tensor`, `shell_tensor_normalized`). With `shell_integral` this is the three-body factorization `pair_density` uses | — |
| `MassiveVolume` | Massive two-body volume: cumulative `(1/4π)∫₀^P r²/(E₁E₂)` (`cumulative_deriv`), `dQ/dP = PQ/(E₁E₂)` (`energy_deriv`), shell density `(1/8π)(2P/Q)` (`shell_density`), `massless_case` (`2P/Q = 1`) | differentiability of the cumulative in `Q` is a hypothesis |

## Decay law, survival and routing

| Modules | Checked result | Retained inputs |
| --- | --- | --- |
| `Survival` | `survive=exp(−Γt)`, positivity, bounds, time constant, half-life | Exponential law |
| `DecayLaw` | Constant per-tick cost from Paper I survival (`ticks_exact`, `ticks_are_survive`), `hazard_pos_iff`, `compounded_limit` (finite→continuum); on the E8 tick `Δ = 43` a width `Γ` (in `m_e`) costs `ΓΔ` per tick and survival after `n` ticks is `exp(−Γ nΔ)` (`substrate_ticks`) | time homogeneity of the update; seconds via the `ħ/(m_e c²)` anchor |
| `Widths` | `lifetime=ħ/Γ`, rescaling, reference-width positivity | Width input |
| `Routing` | `Model` with latency descent and label preservation (recursive routing) | The routing model |

## Scaling bookkeeping and substrate bridge

| Modules | Checked result | Retained inputs |
| --- | --- | --- |
| `MassScaling` | Dimensional exponents `phaseSpaceExponent`, `kinematicDimension`; `three_body_dimensions`; spectrum polynomial | Stipulated contact interaction |
| `ScalingObligations` | Each of the three `M⁵` scaling relations from a derived homogeneity of an actual formula (`momentum_linear`, `dispersion`, …) | The formulas |
| `SubstrateBridge` | `conditional_exponent`: the three scaling relations force the fifth power for `D=4`; E8-internal independence witness; distinct positive cubic/quintic laws | The three relations are proof *inputs* |

## Particles, masses and charges (recorded as tensions)

| Modules | Checked result |
| --- | --- |
| `ChargeProtocols` | Charges from Paper III packets; `thirds`; `integer_iff_colourless` |
| `LeptonMasses` | `m_μ`, `m_τ` written in canonical E8 invariants and decomposed into named tier costs (`muon_ledger`, `tau_ledger`; the `π⁺` ledger is in `PMHadrons.MesonMasses`); muon feedback derived as a recursive fixed point (`muonFeedback_fixpoint`); E8-only enclosures (measured tensions in `tools/e8p/E8PConstants/PMElementaryParticles/LeptonMassPulls.lean`) |
| `QuarkMasses` | Six quark formulas written in canonical E8 invariants and decomposed into named tier costs (`up_ledger`…`top_ledger`); E8-only enclosures (measured pulls in `tools/e8p/E8PConstants/PMElementaryParticles/QuarkMassPulls.lean`) |
| `NeutrinoContext` | Contextual neutrino masses excluded by oscillation data (`weak_minus_rest_excluded`, `no_moderate_gap_ratio`) |
| `TauLifetime` | `τ_τ = τ_μ (m_μ/m_τ)⁵ B_e` (`rate_ratio`, `tau_lifetime_tree`); measured pull in `tools/e8p/E8PConstants/PMElementaryParticles/TauLifetimePulls.lean` |

## Species masses over the wire

The wire is `PMFlavor`/`PMAction`'s generation sector: with no detuning on the reference's wall
(`PMAction.ReferenceDetuning`) the light mass is `M = D_R (δ_O + cyc κ_O)`
(`PMAction.ReferenceWallMass`): one generation with a vector-class carrier (in-cycle, `K = 1`), two
with spinor-class carriers through the reference node (`k/K = α/2`, `PMAction.NodeAmplitude`), and
the other wall's detuning `δ_O`, which must be nonzero (`PMAction.UndetunedWall`). The wire is blind
to the species it carries: one crossing price (`PMConstants.HandoffAdmittance.closure_one_price`),
and the `D₄` geometry with the reference's axis cannot tell up from down
(`PMElementaryParticles.DoubletReflection`). So the wire fixes the form; species are protocols over it, and what
each protocol occupies is open (REVIEW). Earlier per-species scans fitted measured mass ratios and
CKM magnitudes; they were removed as Standard-Model fitting, not substrate results (in git history:
`tools/node_carrier_scan.py`, `tools/reference_wall_mixing_scan.py`, `tools/composite_mass_scan.py`).

## External states

`ExternalStates.persistent_on_shell`: a persisting state
(`PMConstants.OnShell.persistent_single_frequency`) has one energy and one mass on its support, i.e. is
an on-shell mass eigenstate; `branches_do_not_persist` shows cross-branch
superpositions beat. Identifying an external particle with a persisting substrate
state remains a model input.

## Protocols and the 16-channel inventory

Paper V's §4 reads the 16-channel substrate as four base routing protocols, two
routing modes, three anchors and a single sterile vacancy. `ProtocolInventory`
proves the *stipulated* inventory is internally exact and agrees with Paper III:

- `channels_card`: 16 channels (`ν = 16`).
- `two_routing_modes`: 12 route through the colour bulk, 4 do not.
- `hand_split`: 8 active (left-handed boundary), 8 static.
- `anchor_split`: 12 manifold (D=4), 2 boundary (χ=2), 2 unanchored.
- `inventory_split`: up 6, down 6, electron 2, neutrino 1, sterile 1 (= 16).
- `baseProtocol_cases`: exactly four base protocols (`electron`, `up`, `down`, `neutrino`).
- `sterile_iff_no_base`: the sterile vacancy is the unique uncoloured, static,
  unanchored channel.
- `baseProtocol_charge`: the structural classification reproduces Paper III's
  generator charges (`up=2/3`, `down=-1/3`, `electron=-1`, `neutrino=0`).
- `colourBulk_false_iff_leptonic`: the no-colour channels are exactly the
  integer-charge (leptonic) ones (`ChargeProtocols.integer_iff_colourless`).

This checks the paper's enumeration/counting; it does **not** derive the physical
identification of those channels with particles (the paper calls the inventory
stipulated).

**Decay dynamics as routing change (`ProtocolDynamics`).** The paper models decay
as a change of routing protocol. `ProtocolDynamics` makes that concrete on the
inventory: resonant tier labels `Tier = Fin 4` (`Δ⁰…Δ³`), `baseCharge` per base protocol
(up 2/3, down −1/3, electron −1, neutrino 0), and `Decay p ds` = a nonempty exit
cohort with the parent's total charge and every daughter strictly lower-tier.
Proved: `decay_charge` (charge conservation), `decay_tier_lt`, `no_infinite_chain`
(finite descent, matching "at most `L(s₀)` steps"), `tier_zero_terminal`, and the
muon example `muon_decay` (`e+ν+ν̄`, charge `−1 = −1+0+0`). Partial-width addition
and branching normalization are in `Widths` (`branching_normalized`, `total`,
`identical_channels`); competing hazards are in `Survival.competing_hazards`.
**Routing caveats (`ProtocolCaveats`).** The paper states that routing alone does
not force stability or reachability; both are proved as countermodels:
`lower_latency_not_reachable` (a strictly lower-latency, same-label state that is
not a step) and `routing_not_terminal` (a non-terminal state). Together with
`Routing.minimum_terminal` and `Routing.no_infinite_descent` these pin down exactly
what the routing axioms buy. The **specific** allowed routes and rates remain model
inputs. **Tier ladder:** the
tiers are a point (`Δ⁰`), then 1D (`Δ¹`), 2D (`Δ²`), 3D (`Δ³`) — four geometric
tiers. Each protocol's mass ledger occupies a subset (leptons/down 0,1,2; up-type
0,2,3). The draft's earlier "three generations" wording was corrected in
`4_protocols.tex` to this "point then 1,2,3 dimensions" phrasing; no tier beyond
the volume (`Δ⁴`) exists.

## Substrate existence ledger

`SubstrateLedger.substrate_has_components` answers the prior question *does the E8
substrate even have the objects Paper V identifies?* Each conjunct is an existence
witness from the actual Paper II/III constructions: a nontrivial chirality
involution and a rank-two chiral projector (`chirality_exists`,
`chiral_sector_dim_two`); three colour axes and a traceless colour generator
(`colour_axes_exist`, `colour_generator_exists`); the charge spectrum
`{2/3,−1/3,0,−1}` (`charge_values_attained`); all four base protocols plus the
sterile vacancy (`protocols_attained`); and the four-tier ladder
(`tier_ladder_exists`). The physical particle identification remains a proposed
correspondence, not an assertion of this ledger.

## Interpretation boundaries (what is *not* selected)

Proved physics here is **conditional** on a tree-level V−A contact interaction,
massless or specified external states, supplied phase-space normalizations and a
supplied coupling. Not selected: that the contact vertex is the substrate's
physical interaction; the phase-space counting measure, angular density
`1/(32π²)`, electron measure and flux from substrate readout; the absolute
coupling / radiative corrections; the particle/mass ledger; fermionic statistics
and asymptotic-particle interpretation; the decay-law subsystem/environment. The
`M⁵` law is a consequence of the contact model, not a universal rule for every
persistent excitation.

## Verification

Run `./build.sh PMElementaryParticles` for current counts. The sibling `PMAtoms` library is documented
separately in `PMAtoms/`; this file covers only the elementary-particle `PMElementaryParticles`
library.
No Paper VI imports; permitted axioms `propext`, `Classical.choice`, `Quot.sound`.
Run `./build.sh PMElementaryParticles` for current numbers.

## Finite decay machinery

The finite-channel rate layer used at every level (leptons here, hadrons in `PMHadrons`,
nuclei in `PMAtoms`): a rate is `β·c0` times the selected weight of a finite set of open modes,
and the mean life is its inverse.

| Module | Checked result | Retained inputs |
| --- | --- | --- |
| `LatticeSpectral` | Dirichlet eigenvalues of the finite cubic lattice used by the spectral channels | |
| `MeanLife` | `MeanLife lam = 1/lam`; `MeanLife_eq_integral` (integral of `exp(−lam T)`); `MeanLife_eq_survival_integral` (same with `ExponentialFilter.survival`); `persistenceRate = β·costRate`; `meanLife_from_persistence` | the three persistence premises of `HazardForm`; the cost rate and `β` |
| `RateModel` | `channelCost = expectedCost c0 E`; `channelRate_eq : rate = β·c0·Σ prob`; `channelMeanLife = MeanLife (channelRate …)`; zero-probability channels have zero rate | the event family per channel, and the toll/hazard coefficients |
| `BetaLattice` | `BetaLatticeChannel` (`modes`, `active`), `event`, `family`; `betaLatticeRate = β·c0·active/(modes+1)`, `betaLatticeLifetime`, positivity; `betaSpectralWeight = exp(−λ)`, `betaWeightedRate`, `betaSpectralRate`; `betaOpenModes`, `betaSpectralRateCutoff`, positivity, `betaWeightedRate_le`, `betaSpectralRateCutoff_le` (`rate ≤ β·c0`); general gap lemmas `dirichletEigenvalue_mono`, `dirichletEigenvalue_ge_next`, `betaOpenModes_eq_univ_of_twelve_le`, `betaOpenModes_eq_singleton_of_gap`, `betaSpectralRateCutoff_eq_one_of_openModes_eq_univ` | numerical spectral sum / neutron benchmark |
| `LeptonLattice` | finite lepton channel reusing `BetaLattice`; `leptonLatticeRate`, `leptonLatticeLifetime`, positivity | lepton eigenvalue input |
| `LeptonLifetime` | `muonSpectralFraction`, `muonFiniteWidth`, `muonFiniteLifetime`; minimal-cube lepton channel | mass/phase-space coefficient still continuum |

## Results of the 2026-11-16 review

- **The protocols cannot read the wire's spectrum directly** (`PMAction.WireLightBound`; numerical scans
  over each protocol's `δ_O` and cycle phase): up and leptons fail with the linear readout, all three
  with the squared one. The readout is the open item (REVIEW).
- **Doublet structure** (Lean): weak partners are antipodes and native words commute with the antipode (`DoubletSign`); on the wire the antipode is a global sign, so partners are not wire modes (see "Protocols are not wire modes").
- **Map and gate** (Lean): `RefreshMap` (clean active rows are the requirement; clock mask changes
  close over a cycle, `clockRoute_closes`); `CoherentGate` (a full position bit per event for unequal
  angles); the record system has zero margin (`untouched`, `restores_iff_visits`).
- **Withdrawn** (git history has them): everything built on the 2026-11 "corrected" carrier placement:
  the per-protocol margins `64.7 / 18.6 / 11.5`, the information-theory rates `R_p`, the gains and their
  orderings, the second-ratio fits, the up heavy-entry candidate, the protocol-level `U` tests, and the
  same-wire neutrino readout exclusion; `BetaReference` (`β` carrying the up protocol's carrier onto the reference,
  axis-placed protocols) and `UpDownWire` (equal mass product for up and down on the axis-placed wire
  with `(K, k_c, k_s)` on the other wall), both modules removed. Excluded independently of placement: equal gate angles from
  the CC vertex, decay direction, `T₃` or charge squared; exclusion blocking (`2/3`); a wall-dependent
  Wilson `r_O` (`PMAction.WilsonPointForced`); reflection-invariant gains.
