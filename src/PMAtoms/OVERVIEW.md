# PMAtoms — overview of checked results

The map of what the atomic/composite extension proves. Open work is in
[`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md); build instructions are in
[`README.md`](README.md). Sources are under `PMAtoms/`, imported by
`PMAtoms.lean`.

## Hierarchy

```
elementary protocols (PMElementaryParticles)
        │  three colour-axis protocols
        ▼
     Nucleon            (uud / udd, Q = +1 / 0, B = 1)
        │  Z protons + N neutrons
        ▼
     Nucleus            ((Z,N), decay channels, persistence)
        │  electrons = Z for a neutral atom
        ▼
      Atom / Shells     (2n² capacities, hydrogen readouts)
        │  hazards / channels
        ▼
     MeanLife           (τ = 1/λ from the persistence survival)
```

## Modules

| Module | Checked result | Retained inputs |
| --- | --- | --- |
| `Nucleon` | three colour-axis protocols (`slotChannel`); `ChargeProtocols.Q` on the actual channel equals the quark charge (`Q_slotChannel`, `charge_eq_channels`); three colour axes give `B=1` (`baryon_from_three_colours`); proton `uud` `Q=+1`, neutron `udd` `Q=0`, spin `2`, isospin gap `1` | spin-1/2, one protocol per colour axis |
| `Nucleus` | `Q=Z`, `B=Z+N` as sums of nucleon values (`charge_eq_nucleons`, `baryon_eq_nucleons`); `β⁻`, `β⁺`, capture, `α`, fission conserve `Q`/`B` with lepton number on the lepton side; conservation permits a channel from every `(Z,N) ≠ (0,0)` (`conservation_permits_all`); `Persists` is local minimality of a supplied cost; lower-cost daughters vanish by `PersistenceMechanics.Selection` | binding/cost order, allowed routes and rates |
| `NuclearGraph` | `NucleonLabel`, `LinkType` (`pp/pn/nn`), `completeEdgeCount`; `h3_counts` (0,2,1), `he3_counts` (1,2,0), `he4_counts` (1,4,1); `tetrahedron`/degree cap 4; `bindingComplete` decomposition | link weights, tetrahedron closure, packing |
| `NuclearFolding` | `Folding`, `coulombEnergy`, `coulombEnergy_scale`; `softenedKernel a r = 1/√(r²+a²)` with `softenedKernel_scale`, `softenedKernel_le_inv`; `e8ChargeCoupling = πD/(2σ)`; `sphereCoulomb` | actual folded positions | `Folding (A)` positions in `Fin 3`; `dist`; `coulombEnergy`; `dist_scale`; `coulombEnergy_scale : E(λF)=E(F)/λ`; `coulombEnergy_folded` at radius `A^{1/3}` | absolute charge coupling |
| `NuclearCharge` | `qH3/qHe3/qHe4`; `chargeEnergy3_H3 = 3/4`, `chargeEnergy3_He3 = 11/4`, `chargeEnergy4_He4 = 16/5`; `mirror_charge_difference = 2` | absolute coupling scale |
| `NuclearLine` | `lineCounts` gives H-3 `(0,2,1)`, He-3 `(1,2,0)`, He-4 `(1,4,1)`, C-12 `(3,12,3)`, O-16 `(4,16,4)`; `lineBinding_*` decompositions | Coulomb valley, boundary term |
| `AlphaPersistence` | `survivingPhases` count `Δ−gap`; `blockedPhases` count `gap`; `blocked_surviving_card_sum`; `isospinBudget_add_gap`; `alphaCountPhase_eq`; alpha nonneg/zero/capacity bounds |
| `ShapePotential` | `ShapePotential.V`, `Stationary`, `stationary_nonzero`, `discriminant`, `doubleWell`, `doubleWell_min_at_wells`; `e8ShapePotential` (`A=N−152`, `B=Z−96`, `C=χ`); `cubicCoupling=deformationWeight/ν`, `e8CubicPotential`, `nuclearMassPackingCubic`, `e8ShapeShift`, `nuclearMassPackingShape` with supplied β |
| `NuclearDeformation` | `e8DeformationLedger`; quadrupole `σ=5`, pairing `χ=2`; `deformationWeight = shellWeight/(Δ+σ)=43/288`; `deformationExcess = max(P−82,0)`; `deformationBinding`; Z-dependent `deformationZFactor=(Z−82)/(ν−χ)` and `deformationBindingZ`; `nuclearMassPackingDeformed(Z)` candidates; two-shape `mixingMass`/`nuclearMassPackingCoexist` with mixing `V = shellWeight`; `deformationPairingFactor` and `nuclearMassPackingDeformedZPair` |
| `TwoLedger` | `nuclearMass`/`nuclearMassCapped`/`nuclearMassPacking`; `nuclearMassPackingTyped` with `s = σ/ν = 5/16`; `nuclearMassPackingClosure` with `w_c = σ/ν`; `nuclearMassPackingAlpha` with `Δ/D` per alpha cluster and isospin suppression over `Δ`; `nuclearMassPackingShell` with `Z=2(Δ−χ)`, `N=(σ−χ)(Δ−1)` and `Δ/(D+χ)` per excess neutron; `nuclearMassPackingShellPaired` reduces the odd-A shell cost by `(D−1)/D = 3/4`; `alphaCount_eq_budget` proves it is capacity × surviving `Δ`-budget; `mirror_h3_he3_typed` gives `free − 2s − Q_m` | `mirror_h3_he3` is a model identity, not the observed H-3/He-3 mass difference |
| `TwoLedger` | two-ledger mass `nuclearMass`; link asymmetry `±c/2` cancels the charge term; `mirror_h3_he3` proves the mirror is exactly the free `n−p−e` gap |
| `LatticeCharge3Energy` | single-charge energy, `greenCube3_nonneg`, `latticeChargeEnergy3_nonneg`, total response `743/51`, uniform-charge law `q²·743/51` |
| `LatticeCharge3` | exact rational `3×3×3` Green function; nearest `2591/5712`, face `46/119`, body `19/51`; calibrated nearest equals sphere; face and body are below sphere; `cube3Lap_green` certifies the 27-site Laplacian identity |
| `LatticeCharge` | `twoProtonEnergy` on the `2×2×2` cube; nearest pair `46/105`; `twoProtonEnergy_le_nearest`; `latticeChargeEnergy`, `latticeChargeEnergy_single`, `latticeChargeEnergy_zero`; `latticeChargeDifference_neg`; `latticeNormalization`/`normalizedTwoProtonEnergy`; `normalized_nearest_eq_sphere`; `latticeChargeDifferential` (zero at nearest, negative at body diagonal) |
| `LatticeGreen3D` | `greenCube`/`cubeLap` on the `2×2×2` Dirichlet cube; `cubeLap_green`; diagonal `58/315`, nearest `11/315` |
| `LatticeGreen` | `pathGreen N i j = min(i,j)(N+1−max)/(N+1)`; `pathGreen_diag` self-energy; `pathGreen_symm`; exact agreement with `green3`/`green4` | 3D folded lattice |
| `NuclearPacking3D` | `cubeEdges n = 3n²(n−1)` via `cubeEdges_eq_card`; `cubeEdges_per_vertex` (`E/A=3−3/n`), monotonicity and `3/2 ≤ E/A ≤ 3`; typed partition `cubeEdges_channel_partition`, cardinality `cubeEdges_channel_card_sum`; `mixedPP/PN/NN`, `mixedChannelCounts_sum`; `packingClosureRank`, `packingClosureRank_cube`; `cubeInterior`/`cube_interior_iff` selects `3×3×3` as the smallest volume-persistent cube | 3D cubic packing + channel + closure counts |
| `NuclearTopology` | `closed_min_edges` (handshake: min degree 2 ⇒ `A ≤ edges`), `triangle_degree`, `triangle_edges`, `triangle_is_minimal_closed`; `tree_edges`; `cycleRank`, `triangle_cycleRank = 1`, `tetrahedron_cycleRank = 3`, `tree_cycleRank = 0` |
| `AxisSplit` | `axisB` split: reference axis unique (`reference_axis_card = 1`), three colour axes (`colour_axis_card = 3`), `axis_split`, `three_plus_one_axes` |
| `LinkWeights` | `mapWeight = πD`, `boundaryWeight = σ/2`; `ppWeight`, `pnWeight`, `nnWeight`; `base_eq`, `neutron_boundary` tie them to `CompositeMasses` |
| `E8AtomValues` | atom-ladder closure identities: `Δ+σ=(σ−χ)ν`, `2(Δ−χ)=82`, `(σ−χ)(Δ−1)=126`, `2(Δ+σ)=96`, `D(Δ+σ−χ)=184`, `(σ−χ)Δ+(ν+σ+χ)=152`, `(D+χ)(σ−χ)ν=288` |
| `Invariants` | `Δ,ν,σ,χ,D`; `colour_axes`, `reference_axes`, `three_plus_one`, `homo_pair`, `radius_exponent`, `sphere_factor`, `charge_coupling` |
| `NuclearCoordination` | 4 channels = 3 `pn` + 1 homo; `pnCapacity z = (σ−χ)z`, `homoCapacity z = z/χ`; `one_proton_max_neutrons = 3`, `two_proton_max_neutrons = 6`, H-3/He-3/He-4 within capacity |
| `NuclearBinding` | `he4_pairwise_shortfall` (pairwise He-4 predicts 0.017392 u; measured 0.030377), `he4_closure_gap = 0.012985 u`, `mirror_link_difference = 0.000820 u` | link weights |
| `NuclearPacking` | `cliqueEdges`; face sharing `(3/3/9)`, vertex sharing `(7 vertices, 12 edges)`, edge sharing `(6 vertices, 11 edges)`; `packing_laws`; `shared_closure_once` | packing geometry |
| `NuclearSelection` | `GraphCandidate`, `exists_least_graph_cost`, `selectedGraph_min`, `GraphPersists`; `graphs4` enumerates degree-≤4 graphs on 4 vertices, `tetrahedron_mem_graphs4` | cost weights |
| `LinkModes` | `linkSpectrum = [4,1,1]`, row sum 4; `effectiveLinks A light = A + light/2`; `residual_eq_light` identifies the residual with half the light-mode weight | colour/generation light-mode occupation |
| `SystemTower` | `Level` (particle/nucleon/nucleus/atom), `LevelBudget` (toll/margin/sharedLinks, positive cost magnitudes subtracted), `latticeSum`, `boundMass`; `gap_eq_level_budgets` identifies the periodic-table gap with the nucleus+atom budget | the numeric per-level budgets |
| `NuclearMass` | `latticeMass n = Z m_p + N m_n`; `PersistsMass` = no decay lowers it; beta lowers it (`latticeMass_betaMinus_lt`), so `N>0` fails mass-persistence (`not_persistsMass_of_neutron`); α and fission conserve lattice mass (`alpha_mass_eq`, `fission_mass_eq`) | full persistence needs the channel rate/selection |
| `Particle` | `Species` with certified masses and `Q/B/L`; `ParticleDecay` = conserved numbers + lighter products; **`proton_stable`** (baryon number forbids a lighter channel), `neutrino_stable`/`antineutrino_stable` (massless ledger; no lighter channel); allowed `neutron_beta`, `muon_decay`, `pionPlus_decay`, `tau_decay` | certified PM-5 mass enclosures; tree-level channels |
| `ElectronCloud` | `SpinOrbital`, `Cloud = Finset SpinOrbital` (Pauli), `orbitalEnergyEV = −R∞/n²`, `fillCloud` (lowest-n), `AtomSystem.massME` = nucleons + electrons + cloud binding/c² | screening/exchange, electron correlations |
| `FissionYield` | `fissionSplitWith`, `FissionYield`, `fissionYields` (Sn-132 + neighbouring Sn + symmetric), `FissionSplit.lightShellDistance`, `fissionYieldWeight = exp(−(shellWeight/Δ)·d_light)`, `fissionYieldRate`, `fissionYieldLifetime`, `fissionYieldMeasureScale = Δ²/(D+σ) = 1849/9`, `fissionSubshellN1=142`, `fissionSubshellN2=148`, `fissionSubshellCost`, `fissionFullSum`, `fissionFullRate`, `fissionFullLifetime`, `fissionTestNuclei` | E8 fragment-yield weights |
| `FissionSurface` | `FissionSplit`, `symmetricSplit`, `sn132Split`, `fissionSplits`, fragment `shellGain`, `shellCost`, `coulombCost`, `cost`, `fissionSurfaceRate`, `fissionSurfaceLifetime`; finite two-channel surface; `fissionSuperheavyThreshold = 2Δ+2σ+2χ = 100`, `fissionSuperheavyCost = χ·max(Z−100,0)`, `FissionSplit.costWithGovernor` | numerical barrier surface / yields |
| `FissionFissility` | `fissionFissilitySlope = σχ = 10`, `fissionFissilityThreshold = Δ−D = 39`, `fissionScale = 1849/27`, `fissionFragmentShellWeight = 43/6`, `fissionFissilityCost = fissionScale − fissionFissilitySlope(Z²/A−fissionFissilityThreshold)`, `fissionShellCorrection` (N>152 subtracts 43/6), `fissionCostE8`, `fissionRateE8`, `fissionLifetimeE8` | first-principles barrier distribution |
| `FissionFinite` | `fissionCostScale = Δ²/(ν+D+σ+χ) = 1849/27`, `fissionRateScale`, `fissionLifetimeScale` | fissility/Q-dependent barrier set |
| `FissionAsymmetry` | `sn132` (`Z=magic50`, `N=magic82`), `fissionComplement`, `asymmetricFissionChannel`; `sn132_double_magic` | fragment yields and mass split |
| `AlphaConfiguration` | E8 Nilsson parameters `κ=1/ν`, `μ=χ/σ`, `δ=1/σ`; `alphaNilssonGap`, `alphaMixingHindrance = σ/(gap+1/χ) = σχ/(χ·gap+1)`, `alphaMixingHindrance_eq`, `alphaTwoLevel`, `alphaMixingResolvent`, `alphaMixingHindrance_eq_resolvent`; `alphaMixingV = κμδ = 1/200`, `alphaMixedGap`, `alphaMixingHindranceFull`, `alphaMixingHindranceFull_zero`, `alphaCostConfiguredFull`, `alphaLifetimeConfiguredFull`; `alphaCostConfigured`, `alphaLifetimeConfigured`; odd-A only | first-principles mixing amplitudes |
| `AlphaHindrance` | `AlphaLevel`, `AlphaLevel.ofOrbital`, `AlphaLevel.degeneracy`, `spinMismatch`, `parityChange`, `spinDegeneracy`, `alphaCostSpin`; `alphaBlockedNucleons`, `alphaOpenCapacity`, `alphaBlockingHindrance`, `alphaCostBlocked`; `u235Level`, `th231Level`, `pu239Level`, `u235DaughterLevel`, `u235Nuclide`, `pu239Nuclide`, `u235_hindrance_units`, `pu239_hindrance_units`; `u235ParentOrbital`, `th231DaughterOrbital`, `pu239ParentOrbital`, `u235DaughterOrbital`, orbital-level identities; `alphaHindrance`, `alphaCostHindered`, `alphaLifetimeHindered` with supplied hindrance scale | E8 level-ladder derivation of the scale |
| `AlphaFinite` | `alphaFiniteRate = attempt · alphaWidthE8`, `alphaFiniteLifetime`, `alphaWidthE8_eq_phase_barrier`, `alphaFiniteLifetime_ratio`; `alphaWorkload = alphaCapacity`, `alphaFlux = 1/Δ`, `alphaAttempt = cKf`, `alphaFiniteRateE8`, `alphaFiniteLifetimeE8`, positivity; `alphaCostScale = Δ²/(ν+σ)`, `alphaActivation`, `alphaRateScale`, `alphaLifetimeScale`; `alphaCostQ`, `alphaActivationQ`, `alphaRateQ`, `alphaLifetimeQ`; `alphaCostQ2 = (Δ/(D+2χ))Z/√Q − (2Δ−χ)`, `alphaActivationQ2`, `alphaRateQ2`, `alphaLifetimeQ2`; representative `u238`/`cm244`/`cf252` | absolute attempt frequency |
| `CollectiveE8` | `alphaBarrier_eq=43`, `fissionBarrier_eq=43/6`, `e8ClockPeriod_eq=43`; `alphaChannelE8`, `fissionChannelE8`; `alphaBarrierGeiger`, `alphaQ`, `alphaChannelGeiger`; `magicDistance`, `daughterShellGapZ/N`, `daughterShellDistance` (Euclidean; U-238 10, Cm-244 √40, Cf-252 0), `alphaPreformationShell`, `alphaBarrierShellPreformed`, `alphaChannelShellPreformed`; `daughterClosureHindrance`, `alphaPhaseSpace`, `alphaWidthE8`, `alphaMeanLifeE8`, `alphaRelativeLifetimeE8` | frontier-local alpha model; rates/lifetimes |
| `CollectiveRate` | `barrierRate`, `collectiveRate_pos`, `collectiveMeanLife_pos`, `PersistsOn`, `persistsOn_mono`, `persistsOn_nil`, `not_persistsOn_of_lt_meanLife`; `tollTime`, `PersistsAtToll`, `persistsAtToll_iff` |
| `CollectiveRegime` | collective envelope; `alphaChannel`, `fissionChannel`, `alphaChannel_totalMass`, `fissionChannel_totalMass` |
| `CollectiveRegime` | collective/fission channel envelope; `collectiveMass`, `CollectivePersists`, `collectiveMass_eq_parent_of_forall` |
| `FermiFunction` | `coulombEta = ZαE/p`, `fermiFunction = 2πη/(1−e^{−2πη})`; `fermiFunction_pos`, `fermiFunction_ge_one`; `fermiMomentumFactor = F·p` extended at `p=0`, `fermiMomentumFactor_pos`, `one_sub_exp_neg_ge`, `fermiMomentumFactor_le` (bound `p + 2πZαE`) | exact three-body measure and integrability |
| `WeakTransition` | `WeakChannel = Fin (σ−χ)`, `weakChannel_card = 3`, `weakChannelAmplitude`, `weakTransitionHazard`; `weakCurrent`, `weakCurrentWeight`, `weakHazardFromCurrent`; `weakCurrentEntries`, `weakCurrentEntries_norm`, `weakHazardFromEntries_eq`; `weakCarrierEntry`, `weakCarrierEntry_eq_one`, `weakCarrierEntryReal`, `weakCarrierEntries_eq`; `weakCarrierOperator`, `weakCarrierOperator_eq_one`, `weakCarrierOperator_apply`, `weakCarrierOperator_offdiag_zero`, `weakOperatorEntry`, `weakOperatorEntry_eq_entries`; `weakTransitionHazard_eq = G²/3`, `weakHazardFromAmplitude_eq` | equal channel distribution from the weak current |
| `DecayInstantiation` | `betaDecayChannel`, `alphaDecayChannel`, `fissionDecayChannel`; rate-equivalence proofs for beta/alpha/fission split | total fission sum still definitional |
| `NuclearDecay` | `nuclearBetaMinusQ`, `nuclearBetaPlusQ`, `nuclearAlphaQ`, `nuclearFissionQ`; `NuclearMassAllowed`, `betaMinusMassAllowed`, `betaPlusMassAllowed`, `alphaMassAllowed`, `fissionMassAllowed`; Q-equals-channel-mass identities; `nuclearDecayRegime`, `pb/u/cm/cf_nuclearDecayRegime`; `e8NuclearCost`, `persists_e8NuclearCost_of_no_lower`, `not_persists_e8NuclearCost_of_lower`; `NuclearLedgerKind`, `nuclearLedgerKind`, `regimePersists`, `smooth_regimePersists_iff`, `collective_regimePersists_iff`, `cm/cf` selection; `NuclearExit`, `nuclearExits` (β±, α, fission table), `NuclearExit.toChannel`, `nuclearExitChannels`; `pb/u/cm/cf_exitTable_regimePersists_iff`, `cm/cf_alpha_regimePersists_iff` | channel rates/lifetimes |
| `NeutronPrediction` | `neutronCube = 3` (minimal volume-persistent cube), `neutronCutoff`, `neutronCutoffExact`, `neutronSpectralFractionExact`, `neutronLifetimeExactCutoff`, `neutronMarginFactor = alphaPhaseFraction χ = PMSubstrate.E8Margin.phaseMargin = 41/43`, `neutronMargin_survivingPhases`, `neutronMarginFactor_eq_phaseFraction`, `neutronLifetimeCorrected`; `neutronCube_minimal` | numerical fraction is external comparison |
| `BetaCalibration` | `weakAmplitudeSquared = G_F²`, `weakChannelCost = 1/(σ−χ) = 1/3`, `betaHazardE8 = weakAmplitudeSquared · weakChannelCost`, positivity; `betaLifetimeFromFraction`, `betaNeutronLifetimeE8` | independent derivation/validation of the hazard |
| `LeptonLifetime` | `muonSpectralFraction`, `muonFiniteWidth`, `muonFiniteLifetime`; minimal-cube lepton channel | mass/phase-space coefficient still continuum |
| `LeptonLattice` | finite lepton channel reusing `BetaLattice`; `leptonLatticeRate`, `leptonLatticeLifetime`, positivity | lepton eigenvalue input |
| `MesonFiniteChannels` | minimal-cube finite channels for π⁺, K⁺, π⁰; `pion/kaon/neutralPion_openModes`, `*SpectralFraction_eq_one`, `*FiniteWidth`, `*FiniteLifetime`, `*FiniteLifetimeSeconds`, certified bounds | all modes open; finite equals continuum |
| `SpectralWaveBridge` | `spectralFraction`, `spectralDecayChannel`, `spectralDecayChannel_rate/lifetime`, `betaSpectralRate_eq_effectiveWidth`, `spectralAmplitude`, `betaSpectralWeight_eq_normSq_amplitude`, `betaSpectralRate_eq_amplitude_probability`, `spectralDecoherenceRate` | structural bridge to `EffectiveAction`/`DecayChannel` |
| `CollectiveFinite` | finite collective barriers; `collectiveBarrierWeight`, `collectiveFiniteRate`, positivity | barrier set selection |
| `E8Tick` | `e8Tick = Δ = 43`, `lifetimeTicks`; pure E8 period | unit conversion |
| `E8TickUnit` | comparison conversion `electronSecond = ħc/(m_e c²)`, `e8TickSeconds`, `muonLifetimeTicks`, `pionLifetimeTicks`, `kaonLifetimeTicks`, `tauLifetimeTicks`, `neutralPionLifetimeTicks`, `pionLifetimeCorrectedTicks`, `u238FissionTicks`, `cf252FissionTicks`; uses measured unit inputs | not an E8 prediction |
| `SpectralMeasure` | `betaChannelMeasure`, `betaSelectedProbability`, `betaSelectedProbability_nonneg`, `neutronSelectedProbability`, `muonSelectedProbability`; finite spectral weights as a `ChannelMeasure` | numerical normalization |
| `BetaLattice` | `BetaLatticeChannel` (`modes`, `active`), `event`, `family`; `betaLatticeRate = β·c0·active/(modes+1)`, `betaLatticeLifetime`, positivity; `betaSpectralWeight = exp(−λ)`, `betaWeightedRate`, `betaSpectralRate`; `betaOpenModes`, `betaSpectralRateCutoff`, positivity, `betaWeightedRate_le`, `betaSpectralRateCutoff_le` (`rate ≤ β·c0`); general gap lemmas `dirichletEigenvalue_mono`, `dirichletEigenvalue_ge_next`, `betaOpenModes_eq_univ_of_twelve_le`, `betaOpenModes_eq_singleton_of_gap`, `betaSpectralRateCutoff_eq_one_of_openModes_eq_univ` | numerical spectral sum / neutron benchmark |
| `BetaDecay` | `betaDaughter`, `betaQ`, `betaAllowed`, `betaChannel`; `betaWidth = (G Vud)²M²f/(2π³)`, `betaWidth_pos`, `betaLifetime`; `betaEndpoint`, `betaPhaseSpace`, `betaWidthRecoil`, `betaLifetimeRecoil` with supplied Fermi function and radiative factor | supplied nuclear matrix element and Fermi/radiative factors |
| `NuclearLedger` | `certifiedMass = nuclearMassPackingShellPaired` on `certifiedDomain = deformedFrontier`; `certifiedDomain_cm`, `certifiedDomain_cf`, `certifiedMass_decomp` |
| `NuclearRegime` | regime classification through the `Z=96`, `N=152` deformed frontier; `cm_at_frontier`, `cf_beyond_frontier` |
| `SingleParticle` | schematic `nlj` orbital sequence through `126` and `184`; `nuclearOrbitals126_occupation`, `nuclearOrbitals184_occupation`; schematic `orbitalEnergy`, `orbitalLevels`, `cumulativeEnergy`, `smoothEnergy`, `strutinskyCorrection`; `spinOrbit`, `nilssonEnergy`, `nilssonLevels`, `nilssonCumulative`, `nilssonCorrection` |
| `NuclearShells` | `e8ShellLadder`, `e8ShellOccupations` aliases; `nuclearMagic = [2,8,20,28,50,82,96,126,152,184]`, each closure proved as an E8 expression; `nuclearShellSizes = [2,6,12,8,22,32,14,30,26,32]` |
| `Shells` | `orbitalCapacity l = 2(2l+1)`, `shellCapacity n = 2n²`, `shell_capacities : 2,8,18,32` | spin-1/2, angular-momentum degeneracy |
| `Hydrogen` | `rydbergEV_bounds : 13.6056930–13.6056931 eV`; `bohrRadius_bounds : 0.5291772–0.5291773 Å`; `hydrogenLevel_ratio`; `ground_is_lowest` | electron rest energy and `ħc` as unit inputs; certified `α` |
| `ProtocolCandidates` | finite set cohorts (`candidateCohorts`), weak-partner filter (`candidateCohortsWeak`), least-cost selection | set version (multiplicity lost) |
| `ListCohorts` | multiplicity-preserving list cohorts; `charge3`/`listCharge3`, odd fermion parity, weak partner; `muon_list_mem`, `electron_list_not`, `electron_neutrino_list_not` | nuclear candidate set and E8 rates |
| `TransitionSelection` | `TransitionFamily`, `familyCost`; every nonempty candidate set has a least-cost family (`exists_least_cost`); `selectedFamily_min` and `selectedRate_le`; `selected_is_persistence_optimum` | the candidate set of substrate families |
| `RateModel` | `channelCost = expectedCost c0 E`; `channelRate_eq : rate = β·c0·Σ prob`; `channelMeanLife = MeanLife (channelRate …)`; zero-probability channels have zero rate | the event family per channel, and the toll/hazard coefficients |
| `PersistenceRate` | `RateSystem`, `totalRate`, `Persists` = total hazard zero, `not_persists_of_pos`, `MeanLife = 1/totalRate`; least-hazard selection (`exists_least_totalRate`, `selectedSystem_min`) | E8 channel rates |
| `MeanLife` | `MeanLife lam = 1/lam`; `MeanLife_eq_integral` (integral of `exp(−lam T)`); `MeanLife_eq_survival_integral` (same with `ExponentialFilter.survival`); `persistenceRate = β·costRate`; `meanLife_from_persistence` | the three persistence premises of `HazardForm`; the cost rate and `β` |

## E8 provenance audit

| item | status |
| --- | --- |
| spin factor `2` | **derived** from PM-2 `PL.trace = 2` (`Shells.spinStates_eq_trace`); `Nucleon.spinStates` reuses it |
| orbital degeneracy `2l+1` | supplied angular-momentum representation, not derived from E8 |
| `m_e`, `ħc` | supplied unit inputs |
| isotope masses, standard mass numbers, Aufbau order | frozen comparison/display data |
| muon/tau/pion/kaon/quark mass formulas | E8 formulas, but not the six-pillar ledger |
| link-mode occupation | open derivation |

## Mass-formula pillar audit

| particle | formula terms | TOL/MAR counted? | all six pillars? |
| --- | --- | --- | --- |
| proton | `Δ², πD, 1/D, α(D+1/D), Z_TOL, Z_MAR` | yes | **yes** |
| neutron | same + `σ/2` | yes | **yes** |
| muon | `Δσ, χ, π, α` | no | no |
| tau | `Δ²χ, Δσ, χ, D` | no | no |
| π⁰, π⁺ | `α⁻¹, σχ, 1/(ν−χ), …` | no (uses α⁻¹ sum) | no |
| K⁰, K⁺ | `(σ+χ)α⁻¹, σ, Dπ, …` | no | no |
| quarks | `η` and integer counts | no | no |
| electron | supplied `m_e` | no | no |

So the elementary-particle audit is uneven: **only the proton and neutron use the
full six-pillar mass ledger including TOL/MAR**. The leptons, mesons and quarks
use separate E8 formulas (`α⁻¹`, `η`, integer counts) and match experiment, but
they are not the same six-pillar accounting. Re-deriving them in the proton/
neutron ledger is the open unification task.

## What is derived vs input

- Derived: nucleon charge/baryon from substrate channels; shell combinatorics;
  hydrogen readouts from `α`; nuclear conservation and selection structure;
  proton stability; allowed tree-level particle decays.
- Input: spin-1/2, one protocol per colour axis, the `ħc`/`m_e` unit conversions,
  and — crucially — the **nuclear binding/cost order and channel rates**.
- Not yet derived: which `(Z,N)` are stable (the valley), nuclear lifetimes,
  shell filling order, and numeric particle lifetimes (deferred).
