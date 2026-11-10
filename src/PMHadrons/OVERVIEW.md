# PMHadrons — overview of checked results

The map of what the composite level of the E8 substrate proves. Open work is in
[`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md); build instructions are in [`README.md`](README.md).

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

| Module | Checked result | Model inputs (E8 choices not yet derived) |
| --- | --- | --- |
| `Nucleon` | three colour-axis protocols (`slotChannel`); `ChargeProtocols.Q` on the actual channel equals the quark charge (`Q_slotChannel`, `charge_eq_channels`); three colour axes give `B=1` (`baryon_from_three_colours`); proton `uud` `Q=+1`, neutron `udd` `Q=0`, spin `2`, isospin gap `1` | spin-1/2, one protocol per colour axis |
| `Particle` | `Species` with certified masses and `Q/B/L`; `ParticleDecay` = conserved numbers + lighter products; **`proton_stable`** (baryon number forbids a lighter channel), `neutrino_stable`/`antineutrino_stable` (massless ledger; no lighter channel); allowed `neutron_beta`, `muon_decay`, `pionPlus_decay`, `tau_decay` | certified PM-5 mass enclosures; tree-level channels |
| `CompositeMasses` | occupancy-cost formulas for the nucleon/meson composites (E8 values), compared with CODATA 2022 / PDG |  |
| `MesonMasses` | `π⁺` tier ledger (`pionPlus_ledger`, `pionPlus_value`, `pionPlus_mev_value`); `α⁻¹` = six-pillar `cellBudget` (`cellBudget_pillars`; Toll/Margin = `Z_TOL`/`Z_MAR`); every meson = `n·cellBudget + residual` (`*_cells`); `π⁺`, `K⁺`, proton heavier than their current quarks (`*_gt_constituents`) | cell counts `n = χ, σ+χ`; residual terms |
| `Occupancy` | minimum-room principle (`minOccupancy_le`, `not_persistent_of_card_lt`); meson ledgers as the occupancy form `occupancyMass` (`pionPlus_eq_occupancyMass`, `kaonPlus_eq_occupancyMass`); colour neutrality ⇒ ≥ `χ = 2` carriers (`two_le_length_of_colourNeutral`, `occupancy_ge_two_of_colourNeutral`); derived-or-tied (`tied_minimal_of_moved`) | the persistence predicate; the kaon's extra `σ` |
| `StrangeCarrier` | the kaon's extra `σ` identified as the **Protocol** interaction-direction / embedding-address count: `lineFootprint_eq` (a line carrier holds `σ` addresses), `lineFootprint_compl` (`residual_card`), `occupied_add_residual` (`σ + (R_M−σ) = R_M`), `residual_eq` (`R_M−σ = 167`), `mesonOccupancy` (`pion_occupancy = χ`, `kaon_occupancy = χ+σ`), mass links | the premise "a line-tier carrier spans the `σ` directions" |
| `NucleonBase` | the nucleon base `Δ²` is **Margin's causal cone**: `causalCone_eq_sq` (`causal_cone_card`), `causalCone_eq = 1849`, `base_eq_causalCone`, `proton_eq_causalCone` | — (a pillar count, derived) |
| `TollGovernor` | the two transition pillars at the composite level: **Toll** is the emission boundary (`ValidToll`/`tollEvent`; `emissionBoundary_card = 334`, `emissionBoundary_weight = tollTerm` via `uniform_toll`, non-aliasing `167/172` `emission_nonaliasing`, self-aliasing `σ/R_M` `emission_self_aliasing`); **Governor** is cycle persistence (`governorPerSlot` = `χ/Δ = 2/43`, `governorCycleTotal` = `χ`, `governor_restricts`); `cellBudget_eq_six` | the composite configuration still needed for the absolute emission amplitude |
| `CompositeStates` | `SignedState`, `CompositeState`, `compositeCharge`, meson/baryon cohorts; `pionPlus`, `pionZero`, `kaonPlus`, `proton`, `neutron` charges. |  |
| `CompositeBinding` | `BindingLedger`, `compositeMassSq`, positivity/mass-lowering, `compositePhase`; binding energy supplied. |  |
| `CompositeTransition` | `compositeAmplitude`, `CompositeDecay`, `compositeOperator`; `K⁺ → π⁺ π⁰` charge/operator instance. |  |
| `CompositePhaseSpace` | `twoBodyPhaseSpace`, `compositePartialWidth`, `kaonPionT`, `kaonPionPhase`, `kaonPionRate`; K⁺→π⁺π⁰ structural rate with positivity. |  |
| `MultiBodyPhaseSpace` | massless three-body `Φ₃=M²/(128π³)`, `threeBodyRate`, nonnegativity. |  |
| `HadronicMatrixElement` | `BoundStateMatrixElement` with supplied `value`; `kaonPion`, `kaonPionRate`, `kaonPionRate_eq`, `kaonPionRate_nonneg`; explicit nonperturbative-input interface. |  |
| `BoundStateOverlap` | finite constituent `Wavefunction`, `overlap`, `toMatrixElement`, `rate_eq`; overlap as inner product. |  |
| `NeutronRate` | Massive-electron phase space `phaseSpace = ∫ E√(E²−1)(m_n−m_p−E)²`; `g_A = σ/D = 5/4`, `axialFactor = 91/16`; `neutronWidth`, `neutronLifetime`, `beamLifetime`; recoil endpoint `recoilEndpoint`, `phaseSpaceRecoil`, `neutronWidthRecoil`, `neutronLifetimeRecoil` with supplied radiative factor `R` | full Dalitz angular density and derived radiative correction |
| `PionWidth` | two-body `pionWidth(fπ)`, `pionLifetime(fπ)`; `pionDecayConstantE8 = v/(Δ²+Δ−χ)`, `pionWidthTo`, `pionWidthE8`, `pionElectronWidthE8`, `pionLifetimeE8` | `fπ` placeholder `v/(Δ²+Δ−χ)` until the carrier-emission overlap is computed |
| `KaonWidth` | `kaonWidthCKM`, `kaonDecayConstantE8=v/(Δ²−ν²)`, `vusE8=s₁₂c₁₃` (the `(u,s)` entry of `PMFlavor.CKM.ckm`: `vusE8_eq_ckm`), `kaonWidthE8`, `kaonLifetimeE8` | `fK` placeholder `v/(Δ²−ν²)` until the carrier-emission overlap is computed |
| `NeutralPionWidth` | `neutralPionWidthE8 = α²mπ⁰³/(32π³fπ²)`, `neutralPionLifetimeE8`; anomaly coefficient `A = N_c(Q_u²−Q_d²) = 1` from the three colour axes and the protocol charges (`anomalyCoefficient_eq_one`, `neutralPionWidthE8_anomaly`) | triangle-loop normalization `1/(32π³)` |
| `KaonSemileptonic` | leading-order `K_ℓ3` width `G_F²|V_us|² m_K⁵·½·(phase(z)/4)/(192π³)`, `z=(m_π/m_K)²`, `f₊(0)=1`, `m_ℓ→0`; positivity (`kaonL3Width_pos`) | form factor `f₊(t)`, lepton masses, EW/isospin corrections |
| `ParticleChannels` | `ParticleChannel`, `RateStatus`, `totalRate`, `branching`, `totalLifetime`; concrete μ/τ/π/K inventories with provenance labels; `K_ℓ3` at E8 leading order (`e8LeadingOrder`); nonleptonic kaon modes blocked on the bound-state matrix element | hadronic matrix elements |
| `ChannelFinalStateLink` | name-level bridge from `ParticleChannels` (muon, tau, pion, kaon prefixes) to `ParticleFinalStates`; `muon_names`, `tau_first_name`, `pion_names`, `kaon_prefix`, `finalStates_charge_conserved`. |  |
| `MinimalCube` | `CubeVertex`; `cubeInterior`; `cube_interior_iff` (an interior vertex exists iff `n ≥ 3`): the minimal volume-persistent cube is `3×3×3` | |
| `BetaCalibration` | `weakAmplitudeSquared = G_F²`, `weakChannelCost = 1/(σ−χ) = 1/3`, `betaHazardE8 = weakAmplitudeSquared · weakChannelCost`, positivity; `betaLifetimeFromFraction`, `betaNeutronLifetimeE8` | independent derivation/validation of the hazard |
| `WeakTransition` | `WeakChannel = Fin (σ−χ)`, `weakChannel_card = 3`, `weakChannelAmplitude`, `weakTransitionHazard`; `weakCurrent`, `weakCurrentWeight`, `weakHazardFromCurrent`; `weakCurrentEntries`, `weakCurrentEntries_norm`, `weakHazardFromEntries_eq`; `weakCarrierEntry`, `weakCarrierEntry_eq_one`, `weakCarrierEntryReal`, `weakCarrierEntries_eq`; `weakCarrierOperator`, `weakCarrierOperator_eq_one`, `weakCarrierOperator_apply`, `weakCarrierOperator_offdiag_zero`, `weakOperatorEntry`, `weakOperatorEntry_eq_entries`; `weakTransitionHazard_eq = G²/3`, `weakHazardFromAmplitude_eq` | equal channel distribution from the weak current |
| `NeutronPrediction` | `neutronCube = 3` (minimal volume-persistent cube), `neutronCutoff`, `neutronCutoffExact`, `neutronSpectralFractionExact`, `neutronLifetimeExactCutoff`, `neutronMarginFactor = PMSubstrate.E8Margin.phaseMargin = 41/43` (`neutronMarginFactor_eq_substrate`), `neutronLifetimeCorrected`; `neutronCube_minimal` | numerical fraction is external comparison |
| `MesonFiniteChannels` | minimal-cube finite channels for π⁺, K⁺, π⁰; `pion/kaon/neutralPion_openModes`, `*SpectralFraction_eq_one`, `*FiniteWidth`, `*FiniteLifetime`, `*FiniteLifetimeSeconds`, certified bounds | all modes open; finite equals continuum |

## E8 decay checks at this level

| decay | E8 model | comparison | status |
|---|---:|---:|---|
| n → p e ν̄ | 877.2 s | 878 s | E8 finite-spectral + `41/43` margin (`NeutronPrediction`) |
| π⁺ → μ⁺ν | 2.52×10⁻⁸ s | 2.60×10⁻⁸ s | E8 `fπ` |
| K⁺ → μ⁺ν | ≈2.0×10⁻⁸ s | 1.95×10⁻⁸ s | E8 `fK`, `Vus` |
| π⁰ → γγ | ≈8.46×10⁻¹⁷ s | 8.52×10⁻¹⁷ s | E8 `fπ`; anomaly `A = 1` derived |
| K⁺ → π⁰ ℓ⁺ν | leading order | measured rate | E8 `f₊(0)=1`, `m_ℓ→0` (`kaonL3Width`); ~10% low, labelled `e8LeadingOrder` |
