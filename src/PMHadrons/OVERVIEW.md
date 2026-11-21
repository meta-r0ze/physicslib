# PMHadrons — overview of checked results

The map of what the composite level of the E8 substrate proves. Open work is in
[`TODO.md`](TODO.md); build instructions are in [`README.md`](README.md).

Downstream code (`PMAtoms`, `e8p`) imports `PMHadrons.Values`: nucleon and meson masses,
decay constants, the corrected lifetimes and their bounds, the K/π ratio, the neutron margin and
the Toll/Governor emission names (same pattern as `PMElementaryParticles.Values`).

## Place in the tower

A composite is a cohort of elementary carriers (`PMElementaryParticles`) that persists together
as a new system on the substrate. Its **mass is the occupancy cost**: the mesons are a whole
number of substrate cells, each cell paying the six-pillar budget `α⁻¹`, plus a short residual
(`n·α⁻¹ + residual`); the nucleons are a `Δ²` base minus pillar costs. Its **decays are
rearrangements** of that cohort, priced by the same pillars. The nucleons are the template: the
nucleus ledger (`PMAtoms.LinkWeights`) reuses their `πD` and `σ/2` terms.

The mass is not "constituents minus a binding budget": every composite is far heavier than its
current carriers (`MesonMasses.*_gt_constituents`), and the mass is set by the occupancy, not by
the constituent list.

The **occupancy** is the least number of cells a *persistent* placement holds (`Occupancy`):
every persistent placement holds at least `n`, and a placement below `n` has nowhere to stand and
rearranges (`minOccupancy_le`, `not_persistent_of_card_lt`). A colour-neutral composite needs at
least two carriers, hence at least `χ = 2` cells (`occupancy_ge_two_of_colourNeutral`).

Both bases are **pillar counts**: a meson holds `χ + σ·ℓ` cells — the Map base `χ` plus the
Protocol interaction-direction count `σ` per line-tier carrier (`StrangeCarrier`) — and the
nucleon base `Δ²` is Margin's causal cone of one cycle (`NucleonBase`). The persistence predicate
and the premise "a line-tier carrier spans the `σ` directions" remain inputs.

Standard-Model names (proton, neutron, pion, kaon) are **comparison labels** throughout this
file; a measured value or a `σ` in a column is a comparison, not an input.

Shared units and couplings (`me`, `ħc`, `α`, `α⁻¹`, their bounds, `G_F` in `m_e⁻²`) live in
`PMElementaryParticles.SharedUnits` and are re-exported here by `CompositeMasses` and
`NeutronRate`.

## Mass-formula pillar audit

| particle | formula terms | TOL/MAR counted? | all six pillars? |
| --- | --- | --- | --- |
| proton | `Δ², πD, 1/D, α(D+1/D), Z_TOL, Z_MAR` | yes | **yes** |
| neutron | same + `σ/2` | yes | **yes** |
| muon | `Δσ, χ, π, α` | no | no |
| tau | `Δ²χ, Δσ, χ, D` | no | no |
| π⁰, π⁺ | `χ·α⁻¹` + residual `−σχ + 1/(ν−χ) (+ σ + D − α(σ−χ)/χ)` | yes, `χ` times via `α⁻¹` | **yes** (`pion0_cells`, `pionPlus_cells`) |
| K⁰, K⁺ | `(σ+χ)·α⁻¹` + residual `−σ + Dσ − 2π/(ν−χ)` / `−σ + Dπ − 1/√2 − α(σ−χ)/χ` | yes, `σ+χ` times via `α⁻¹` | **yes** (`kaon0_cells`, `kaonPlus_cells`) |
| quarks | `η` and integer counts | no | no |
| electron | supplied `m_e` | no | no |

`α⁻¹` is, by definition, one substrate cell's six-pillar budget
(`PMSubstrate.impedance`; `MesonMasses.cellBudget_pillars`): a cell "has all six components"
because its cost is the sum of all six pillar terms. Its Toll and Margin terms are exactly the
nucleons' `Z_TOL` and `Z_MAR` (`tollTerm_eq_zTol`, `marginTerm_eq_zMar`). So **the nucleons and
the mesons all carry the six pillars including TOL/MAR**, in two forms: the nucleons as a `Δ²`
base minus pillar costs, the mesons as `n` whole cell budgets plus a residual. The **occupancy**
`n` (how many cells the persistent configuration holds) and the residuals are the model inputs
under study. The leptons and quarks still use separate E8 formulas (`η`, integer counts); that
is elementary-particle work.

## Modules

Grouped by topic. `MinimalCube` moved to `PMAction.MinimalCube` (Nov 2026). Several decay modules are
labelled candidate or comparison in their headers; the neutron has one scored route
(`NeutronContinuum`); `NeutronRate` holds its formulas and `NeutronPrediction` the finite-cube
comparison.

### Composites and their masses

| Module | Checked result | Model inputs (E8 choices not yet derived) |
| --- | --- | --- |
| `Nucleon` | three colour-axis protocols (`slotChannel`); `ChargeProtocols.Q` on the actual channel equals the quark charge (`Q_slotChannel`, `charge_eq_channels`); three colour axes give `B=1` (`baryon_from_three_colours`); proton `uud` `Q=+1`, neutron `udd` `Q=0`, spin `2`, isospin gap `1` | spin-1/2, one protocol per colour axis |
| `CompositeStates` | `SignedState`, `CompositeState`, `compositeCharge`, meson/baryon cohorts; `pionPlus`, `pionZero`, `kaonPlus`, `proton`, `neutron` charges. |  |
| `CompositeMasses` | occupancy-cost formulas for the nucleon/meson composites (E8 values), compared with CODATA 2022 / PDG |  |
| `MesonMasses` | `π⁺` tier ledger (`pionPlus_ledger`, `pionPlus_value`, `pionPlus_mev_value`); `α⁻¹` = six-pillar `cellBudget` (`cellBudget_pillars`; Toll/Margin = `Z_TOL`/`Z_MAR`); every meson = `n·cellBudget + residual` (`*_cells`); `π⁺`, `K⁺`, proton heavier than their current quarks (`*_gt_constituents`) | cell counts `n = χ, σ+χ`; residual terms |
| `Occupancy` | minimum-room principle (`minOccupancy_le`, `not_persistent_of_card_lt`); meson ledgers as the occupancy form `occupancyMass` (`pionPlus_eq_occupancyMass`, `kaonPlus_eq_occupancyMass`); colour neutrality ⇒ ≥ `χ = 2` carriers (`two_le_length_of_colourNeutral`, `occupancy_ge_two_of_colourNeutral`); derived-or-tied (`tied_minimal_of_moved`) | the persistence predicate; the kaon's extra `σ` |
| `StrangeCarrier` | the kaon's extra `σ` identified as the **Protocol** interaction-direction / embedding-address count: `lineFootprint_eq` (a line carrier holds `σ` addresses), `lineFootprint_compl` (`residual_card`), `occupied_add_residual` (`σ + (R_M−σ) = R_M`), `residual_eq` (`R_M−σ = 167`), the **direction register** (`directionRegister`, `directionRegister_card`, `line_register_card`), `mesonOccupancy` / `mesonOccupancy_eq_register` (`pion_occupancy = χ`, `kaon_occupancy = χ+σ`), `meson_ledgers` | — (dir register: a line carrier holds the whole `σ` direction register, as a boundary holds its orientations) |
| `NucleonBase` | the nucleon base `Δ²` is **Margin's causal cone**: `causalCone_eq_sq` (`causal_cone_card`), `causalCone_eq = 1849`, `base_eq_causalCone`, `proton_eq_causalCone` | — (a pillar count, derived) |
| `AxialCount` | `g_A` step 1, the nucleon's spin-flip count on the 64 three-carrier states: vector `1` (`vector_count`), axial `5/3` (`axial_count`, `axial_ratio`), `5/3 = σ/(σ−χ)` (`axial_ratio_eq_invariants`); the measured `1.2754` is `0.765` of it | step 2, the reduction from confined motion |
| `SpinFlavour` | the SU(6) spin-flavour algebra on three quarks with literal vectors: `sumG2` (`ΣG²`), `sumG2_proton = 57/16`, `sumG2_delta = 33/16`, `neutron_margin_pos`, `pion_margin_pos`; the double-commutator checks are in `tools/slow/SpinFlavourDC.lean` (outside the build) | the nucleon/Δ split used by `PILLARS.md` |
| `CubeScales` | the lepton cube (neutron final state, units `m_e`) and the carrier cube (confined carrier, units `ħc/a`) cannot share one spacing: `single_unit_rms_bound`, `two_units` (the carrier unit exceeds the lepton unit by more than `300`) | the carrier rms radius `ρ = 1.354` (numerical) |

### Pillars of emission

| Module | Checked result | Model inputs (E8 choices not yet derived) |
| --- | --- | --- |
| `TollGovernor` | the two transition pillars at the composite level: **Toll** is the emission boundary (`ValidToll`/`tollEvent`; `emissionBoundary_card = 334`, `emissionWeight = tollTerm` via `uniform_toll`, non-aliasing `167/172` `emission_nonaliasing`, self-aliasing `σ/R_M` `emission_self_aliasing`); **Governor** is cycle persistence (`governorPerSlot` = `χ/Δ = 2/43`, `governorCycleTotal` = `χ`, `governor_restricts`); `cellBudget_eq_six` | the composite configuration still needed for the absolute emission amplitude |
| `Emission` | the composite emission overlap and width: `emissionOverlap` (composite configuration vs outgoing carrier — the SM comparison's `fπ`/`fK`), `emissionWidth = emissionWeight · |overlap|² · phaseSpace`, `emissionWidth_eq_partialWidth` (`= |T|²·phaseSpace` with `T = √emissionWeight·overlap`), positivity | the composite configuration (the overlap value) |
| `EmissionScale` | the emission configuration is the persistence-selected **uniform** law (`emission_configuration_uniform`), so `fπ = v/|Ω_π|`; **no-go**: the emission mode count is **not** the occupancy (`occupancy_reading_excluded` — `fK/fπ > 1` while `χ/(σ+χ) = 2/7 < 1`); `pionModes = 1890 = causalCone + (Δ−χ)`, `kaonModes = 1593` | the emission mode space (separate from the occupancy) |
| `EmissionSpace` | the pion's emission space as a set: Margin's one-cycle cone plus the Governor's surviving phases, `pionEmission_card = 1890`; six candidate kaon rules (enumerated outside Lean) all miss FLAG `fK/fπ` | the kaon's rule (open) |

### Weak decays: charged current and normalization

| Module | Checked result | Model inputs (E8 choices not yet derived) |
| --- | --- | --- |
| `ChargedCurrentRate` | one charged-current normalization, each factor once: `Γ(P → μν(γ)) = G_F² |qV|² f_P² m_P m_μ²(1 − m_μ²/m_P²)²/(8π)·(1 + δ_P)` with PMFlavor's dressing `q² = 515/516` and the supplied full radiative correction (`δ_π = 0.0176`, `δ_K = 0.0107`); `pionMuLifetimeSeconds_bounds` `2.61592–2.61602×10⁻⁸ s`, `kaonMuLifetimeSeconds_bounds` `1.99692–1.99700×10⁻⁸ s`, `kaonPionRatioRadiative_bounds` `1.309978–1.309980`; replaces the fitted `32/33` and `sharedFactor` | `δ_P` (its short-distance part is `ShortDistanceRunning`'s `R`) |
| `ShortDistanceRunning` | the one-loop photon running of the weak contact from the E8 W scale to the E8 proton, `R = 1 + (3α/4π)(1+2Q̄) ln(m_Z²/m_p²)`: `runningFactor_bounds` `1.021178–1.021180`; it matches `sharedFactor = (32/33)/|V_ud|²` to `< 7·10⁻⁵` (`runningFactor_sub_shared`), not exactly | matching and finite parts |
| `DecayInstantiation` | (earlier stage, superseded for the mesons by `ChargedCurrentRate`) pion, kaon and neutron in `PersistenceMechanics.DecayChannel`'s slots (toll, capacity, map, protocol, governor, margin); one shared margin `R = (32/33)/|V_ud|²` for all three (`pionChannelCKM_rate`, `kaonChannelCKM_rate`, `neutronChannelCKM_lifetime`); an earlier `41/43` neutron correction amounted to a Governor above one and was removed | `R` not derived (see `ShortDistanceRunning`) |
| `KaonPionRatio` | `Γ_K/Γ_π` with `|V_us|²` and `|V_ud|²` on the two widths, common factors cancelling: `1.318922…` (`kaonPionWidthRatio_bounds`), `fK/fπ = 1890/1593 = 70/59` | `fK` count |
| `PionWidth` | two-body `pionWidth(fπ)`, `pionLifetime(fπ)`; `pionDecayConstantE8 = v/(Δ²+Δ−χ)`, `pionWidthTo`, `pionWidthE8`, `pionElectronWidthE8`, `pionLifetimeE8` | `fπ` placeholder `v/(Δ²+Δ−χ)` until the carrier-emission overlap is computed |
| `KaonWidth` | `kaonWidthCKM`, `kaonDecayConstantE8=v/(Δ²−ν²)`, `vusE8=s₁₂c₁₃` (the `(u,s)` entry of `PMFlavor.CKM.ckm`: `vusE8_eq_ckm`), `kaonWidthE8`, `kaonLifetimeE8` | `fK` placeholder `v/(Δ²−ν²)` until the carrier-emission overlap is computed |
| `NeutralPionWidth` | `neutralPionWidthE8 = α²mπ⁰³/(32π³fπ²)`, `neutralPionLifetimeE8`; anomaly coefficient `A = N_c(Q_u²−Q_d²) = 1` from the three colour axes and the protocol charges (`anomalyCoefficient_eq_one`, `neutralPionWidthE8_anomaly`) | triangle-loop normalization `1/(32π³)` |
| `KaonSemileptonic` | leading-order `K_ℓ3` width `G_F²|V_us|² m_K⁵·½·(phase(z)/4)/(192π³)`, `z=(m_π⁰/m_K⁺)²` from the E8 mass ledgers, `f₊(0)=1`, `m_ℓ→0`; positivity (`kaonL3Width_pos`), with `l3Z_lt_charged_ratio` verifying the kinematic change | form factor `f₊(t)`, lepton masses, EW/isospin corrections |
| `MesonFiniteChannels` | minimal-cube finite channels for π⁺, K⁺, π⁰; `pion/kaon/neutralPion_openModes`, `*SpectralFraction_eq_one`, `*FiniteWidth`, `*FiniteLifetime`, `*FiniteLifetimeSeconds`, certified bounds; `pionLifetimeCorrectedSeconds` (`32/33` margin, tight bounds) | all modes open; finite equals continuum |

### Weak decays: the neutron

| Module | Checked result | Model inputs (E8 choices not yet derived) |
| --- | --- | --- |
| `NeutronContinuum` | the neutron on the continuum route (the emitted electron is not confined, so its modes are the lattice's continuum limit): `phase_integral` (closed-form `f`, proved as the integral), `coulomb_linear_integral`, `neutronContinuum_rate` (`Γ = G_F²|V_ud|²R(1+3g_A²)f/(2π³)`), lifetime bounds without and with the Fermi factor's leading term | the E8 neutron lifetime; see `src/PMElementaryParticles/CONTINUOUS.md` |
| `NeutronRate` | Massive-electron phase space `phaseSpace = ∫ E√(E²−1)(m_n−m_p−E)²`; `g_A = σ/D = 5/4`, `axialFactor = 91/16`; `neutronWidth`, `neutronLifetime`, `beamLifetime`; recoil endpoint `recoilEndpoint`, `phaseSpaceRecoil`, `neutronWidthRecoil`, `neutronLifetimeRecoil` with supplied radiative factor `R` | full Dalitz angular density and derived radiative correction |
| `NeutronPrediction` | the finite `3×3×3` neutron channel (comparison; PMAtoms' finite-cube instances use it): `neutronCube = 3`, `neutronCutoff`, `neutronCutoffExact`, `neutronSpectralFractionExact`, `neutronLifetimeExactCutoff`, `neutron_openModes`, `neutronMarginFactor = E8Margin.phaseMargin = 41/43` (used by PMAtoms), exact-cutoff enclosures for `DecayInstantiation`; the earlier `41/43` corrected lifetime is removed | numerical fraction is external comparison |
| `BetaCalibration` | `weakAmplitudeSquared = G_F²`, `weakChannelCost = 1/(σ−χ) = 1/3`, `betaHazardE8 = weakAmplitudeSquared · weakChannelCost`, positivity; the three weak channels behind `/3` (`WeakChannel = Fin (σ−χ)`, `weakTransitionHazard_eq = G²/3`, the equal-weight carrier operator; formerly `WeakTransition`); `betaLifetimeFromFraction`, `betaNeutronLifetimeE8` | independent derivation/validation of the hazard |

### Channel inventory and interfaces

| Module | Checked result | Model inputs (E8 choices not yet derived) |
| --- | --- | --- |
| `Particle` | `Species` with certified masses and `Q/B/L`; `ParticleDecay` = conserved numbers + lighter products; **`proton_stable`** (baryon number forbids a lighter channel), `neutrino_stable`/`antineutrino_stable` (massless ledger; no lighter channel); allowed `neutron_beta`, `muon_decay`, `pionPlus_decay`, `tau_decay` | certified PM-5 mass enclosures; tree-level channels |
| `ParticleChannels` | `ParticleChannel`, `RateStatus`, `totalRate`, `branching`, `totalLifetime`, `modeledLifetime`; concrete μ/τ/π/K inventories with provenance labels; `K_ℓ3` at E8 leading order (`e8LeadingOrder`); nonleptonic kaon modes blocked on the bound-state matrix element | hadronic matrix elements |
| `CompositeTransition` | `compositeAmplitude`, `CompositeDecay`, `compositeOperator`; `K⁺ → π⁺ π⁰` charge/operator instance. |  |
| `CompositePhaseSpace` | `twoBodyPhaseSpace`, `compositePartialWidth`, `kaonPionT`, `kaonPionPhase`, `kaonPionRate`; K⁺→π⁺π⁰ structural rate with positivity. |  |
| `HadronicMatrixElement` | `BoundStateMatrixElement` with supplied `value`; `kaonPion`, `kaonPionRate`, `kaonPionRate_eq`, `kaonPionRate_nonneg`; explicit nonperturbative-input interface. |  |
| `BoundStateOverlap` | finite constituent `Wavefunction`, `overlap`, `toMatrixElement`, `rate_eq`; overlap as inner product. |  |

The muon inventory uses the inclusive rate from `MuonLifetimeHigherOrder`.
The pion and kaon muonic entries use the photon-inclusive partial rates from
`ChargedCurrentRate`. The three entries carry `.modelInput` because their
radiative terms are supplied. Their natural-unit rates use
`PhysicalUnits.electronTime / τ_seconds`, and the round-trip theorems recover
the same lifetimes that e8p reports.

`modeledLifetime` returns a value for a positive sum when every listed
channel has an assigned rate. It returns `none` for the current kaon list
because the nonleptonic entries are blocked. `totalRate` and `totalLifetime`
retain the arithmetic of the listed rates for partial-sum calculations.

The conditional tau inventory uses the supplied electronic fraction `B_e`,
sets `B_μ = B_e · MassiveWidth.phase TauBranching.r`, and assigns the residual
`1 − B_e − B_μ` to hadrons. `tau_leptonic_ratio` verifies the width ratio
and `tau_channel_sum` verifies the total. The inclusive quark-current width
needed to predict `B_e` is tracked in REVIEW.

## E8 decay checks at this level

Values as e8p reports them (`tools/e8p/e8p_output.txt`); a `σ` is a comparison, not an input.

| decay | E8 model | comparison | status |
|---|---:|---:|---|
| n → p e ν̄ | 923.37–923.39 s (`NeutronContinuum.neutronLifetimeContinuumCoulombSeconds_bounds`: continuum route, E8 `G_F`, `|V_ud|²R = 32/33`, `g_A = 5/4`, `α`, `m_n − m_p`, leading Coulomb) | 878.4 ± 0.5 s (PDG 2024; +5.1%) | the electron's outer radiative correction (numerical, `tools/neutron_rc_certificate.py`) gives about 909 s; the rest is `g_A`'s electromagnetic matching (REVIEW) |
| π⁺ → μ⁺ν | 2.61592–2.61602×10⁻⁸ s (`ChargedCurrentRate.pionMuLifetimeSeconds_bounds`: dressed `|V_ud|`, supplied `δ_π`) | 2.60362×10⁻⁸ s, the inclusive muonic partial (τ/BR); +0.47% | the residual is `f_π`: the measurement implies `130.58(13)` MeV against E8 `v/1890 = 130.275` (−0.24%) |
| K⁺ → μ⁺ν(γ) | 1.99692–1.99700×10⁻⁸ s (`ChargedCurrentRate.kaonMuLifetimeSeconds_bounds`, e8p `kaon_muonic_partial_lifetime_s`) | 1.9478×10⁻⁸ s from τ/BR (+2.5%) | the residual is `f_K`: implied `156.6` MeV against E8 `v/1593 = 154.56` (−1.3%). e8p shows the lifetime for context alongside the scored K/π ratio, which shares its comparison inputs |
| `Γ_K/Γ_π` | 1.309978–1.309980 (`kaonPionRatioRadiative_bounds`, with `(1+δ_K)/(1+δ_π)`) | 1.3367 ± 0.0032 (−2.0%) | `fK/fπ = 70/59` against FLAG `1.1934` |
| π⁰ → γγ | 8.44–8.48×10⁻¹⁷ s (two-photon partial) | 8.530×10⁻¹⁷ s (τ/BR(γγ); −0.5σ) | E8 `fπ`; anomaly `A = 1` derived; triangle normalization supplied |
| K⁺ → π⁰ ℓ⁺ν | leading order (`kaonL3Width`) with E8 `m_π⁰` | — | numerical check: the neutral-pion assignment raises the massless phase factor by about 3.7% relative to the previous charged-pion assignment |
