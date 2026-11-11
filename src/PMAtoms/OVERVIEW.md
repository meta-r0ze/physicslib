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
     Nucleon            (uud / udd, Q = +1 / 0, B = 1)   [PMHadrons]
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
| `NuclearPacking3D` | `cubeEdges n = 3n²(n−1)` via `cubeEdges_eq_card`; `cubeEdges_per_vertex` (`E/A=3−3/n`), monotonicity and `3/2 ≤ E/A ≤ 3`; typed partition `cubeEdges_channel_partition`, cardinality `cubeEdges_channel_card_sum`; `mixedPP/PN/NN`, `mixedChannelCounts_sum`; `packingClosureRank`, `packingClosureRank_cube`; the smallest volume-persistent cube `3×3×3` (`PMHadrons.MinimalCube.cube_interior_iff`) | 3D cubic packing + channel + closure counts |
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
| `FragmentOverlap` | the α/fission fragment overlap (the hadron `Emission` analogue): `fragmentOverlap`, `fragmentWidth = barrierRate · overlap² · phase`, `fragmentWidth_eq_partialWidth` (= `T²·phase` with `T = √barrierRate · overlap`), positivity | the fragment configuration (the overlap value) |
| `NuclearRateUnit` | the Governor attempt frequency candidate: `attemptFrequency = χ/Δ = 2/43` (`attemptFrequency_eq`), `governorChannelRate_eq` (= `RateModel.channelRate` with `β·c0 = χ/Δ`). Compared with the α table (`ALPHA-TESTS.md`): the capacity attempt `min(Z,N)/(2Δ)` used by `AlphaFinite` is closer | the identification `β·c0 = χ/Δ` |
| `NuclearOccupancy` | the nucleus occupancy `A = Z + N`, the closure predicates (`ProtonClosed`/`NeutronClosed`/`DoublyClosed`), the frontier closure pair (`frontier_doublyClosed`: `Z=96`, `N=152`; `frontier_occupancy = 248`) | the saturation / deformation cost functional |
| `PersistenceSelection` | the exit table wired into the rate layer: `nuclearExitRateSystem`, `nuclearExitRateSystem_totalRate`, `nuclearPersistsOn_iff`, `selectedNuclide_min` | the barrier/rate unit (`NuclearRateUnit`) |
| `CollectiveRegime` | collective envelope; `alphaChannel`, `fissionChannel`, `alphaChannel_totalMass`, `fissionChannel_totalMass` |
| `CollectiveRegime` | collective/fission channel envelope; `collectiveMass`, `CollectivePersists`, `collectiveMass_eq_parent_of_forall` |
| `FermiFunction` | `coulombEta = ZαE/p`, `fermiFunction = 2πη/(1−e^{−2πη})`; `fermiFunction_pos`, `fermiFunction_ge_one`; `fermiMomentumFactor = F·p` extended at `p=0`, `fermiMomentumFactor_pos`, `one_sub_exp_neg_ge`, `fermiMomentumFactor_le` (bound `p + 2πZαE`) | exact three-body measure and integrability |
| `DecayInstantiation` | `betaDecayChannel`, `alphaDecayChannel`, `fissionDecayChannel`; rate-equivalence proofs for beta/alpha/fission split. Pillar-resolved versions `betaPillarChannel`, `alphaPillarChannel`, `fissionPillarChannel`, `fissionYieldPillarChannel` put each factor in its own slot (workload → capacity, flux/`c0` → toll, closure hindrance → map, preformation → protocol, superheavy gate → governor, yield weight → margin, barrier → action), each with the same rate (`*_rate_eq`) | total fission sum still definitional |
| `PersistenceComplex` | the packing as one complex: `packingFaces`, `packingCells` (`3n(n−1)²`, `(n−1)³` at `A = n³`); `packing_euler` (`V − E + F − C = 1`); `packingClosureRank_eq_faces_sub_cells` (cycle rank = faces − cubes); `phaseMargin_eq_one_add_governor` (`41/43 = 1 + governorTerm`); `alphaPhaseFraction_eq_governor` (`1 − gap/Δ`); `neutronMargin_eq_phaseMargin`; `neutronMargin_survivingPhases`, `neutronMarginFactor_eq_phaseFraction` (the neutron margin is the alpha phase fraction at gap `χ`) | |
| `NuclearDecay` | `nuclearBetaMinusQ`, `nuclearBetaPlusQ`, `nuclearAlphaQ`, `nuclearFissionQ`; `NuclearMassAllowed`, `betaMinusMassAllowed`, `betaPlusMassAllowed`, `alphaMassAllowed`, `fissionMassAllowed`; Q-equals-channel-mass identities; `nuclearDecayRegime`, `pb/u/cm/cf_nuclearDecayRegime`; `e8NuclearCost`, `persists_e8NuclearCost_of_no_lower`, `not_persists_e8NuclearCost_of_lower`; `NuclearLedgerKind`, `nuclearLedgerKind`, `regimePersists`, `smooth_regimePersists_iff`, `collective_regimePersists_iff`, `cm/cf` selection; `NuclearExit`, `nuclearExits` (β±, α, fission table), `NuclearExit.toChannel`, `nuclearExitChannels`; `pb/u/cm/cf_exitTable_regimePersists_iff`, `cm/cf_alpha_regimePersists_iff` | channel rates/lifetimes |
| `SpectralWaveBridge` | `spectralFraction`, `spectralDecayChannel`, `spectralDecayChannel_rate/lifetime`, `betaSpectralRate_eq_effectiveWidth`, `spectralAmplitude`, `betaSpectralWeight_eq_normSq_amplitude`, `betaSpectralRate_eq_amplitude_probability`, `SpectralDecoherenceChannel`, `spectralMeanCost`, `spectralDecoherenceChannel`, `spectralDecoherenceRate` | structural bridge to `EffectiveAction`/`DecayChannel`; phase cost is a model input |
| `SpectralDecoherenceInstances` | `muon/neutron/pion/kaon/neutralPionDecoherenceChannel`, corresponding `*_rate` theorems | same finite spectra; phase cost kept separate from population lifetime |
| `CollectiveWaveBridge` | `collectiveFraction`, `collectiveDecayChannel`, `collectiveDecayChannel_rate/lifetime`, `collectiveFiniteRate_eq_effectiveWidth`, `collectiveAmplitude`, `collectiveBarrierWeight_eq_normSq_amplitude`, `collectiveFiniteRate_eq_amplitude_probability`, `collectiveMeanBarrier`, `collectiveDecoherenceChannel` | alpha/fission barrier weights as wave probabilities; phase cost model input |
| `NuclearExitWaveBridge` | `nuclearExitBarrier`, `nuclearExitFraction`, `nuclearExitDecayChannel`, `nuclearExitDecoherenceChannel`, rate/lifetime theorems | standard β⁻/β⁺/α/fission exit table in the wave/decay form |
| `CollectiveFinite` | finite collective barriers; `collectiveBarrierWeight`, `collectiveFiniteRate`, positivity | barrier set selection |
| `E8Tick` | `e8Tick = Δ = 43`, `lifetimeTicks`; pure E8 period | unit conversion |
| `ClockHierarchy` | `nestedPeriod`, `nestedFlux`, `parallelRate`, `serialLifetime`, `clockDividedRate`, positivity and product identities; `nestedPeriod_10_2_6 = 5160` | composition law is a model question |
| `AlphaClockComparison` | `capacityPeriod`, `gatedPeriod`, `alphaAttempt_eq_inv_capacityPeriod`, `alphaNestedAttempt`, `capacity_vs_nested_ratio = workload²` | current capacity convention contrasted with nested clocks |
| `E8TickUnit` | comparison conversion `electronSecond = ħc/(m_e c²)`, `e8TickSeconds`, `muonLifetimeTicks`, `pionLifetimeTicks`, `kaonLifetimeTicks`, `tauLifetimeTicks`, `neutralPionLifetimeTicks`, `pionLifetimeCorrectedTicks`, `u238FissionTicks`, `cf252FissionTicks`; uses measured unit inputs | not an E8 prediction |
| `SpectralMeasure` | `betaChannelMeasure`, `betaSelectedProbability`, `betaSelectedProbability_nonneg`, `neutronSelectedProbability`, `muonSelectedProbability`; finite spectral weights as a `ChannelMeasure` | numerical normalization |
| `BetaDecay` | `betaDaughter`, `betaQ`, `betaAllowed`, `betaChannel`; `betaWidth = (G Vud)²M²f/(2π³)`, `betaWidth_pos`, `betaLifetime`; `betaEndpoint`, `betaPhaseSpace`, `betaWidthRecoil`, `betaLifetimeRecoil` with supplied Fermi function and radiative factor | supplied nuclear matrix element and Fermi/radiative factors |
| `NuclearLedger` | `certifiedMass = nuclearMassPackingShellPaired` on `certifiedDomain = deformedFrontier`; `certifiedDomain_cm`, `certifiedDomain_cf`, `certifiedMass_decomp` |
| `CertifiedNumerics` | `cbrt` (binary-search integer cube root, `cbrt_spec`); computable `ℚ` bounds `rpow23Lo`/`rpow23Hi`/`sqrtLo`/`sqrtHi` with `rpow23_bounds_auto`/`sqrt_add_one_bounds_auto`; interval API `mul_bounds`, `inv_bounds` | interval analysis (treated as analysis, not selection) |
| `CertifiedEnclosure` | `packingBindingTyped_eq`, `chargeTermSphere_eq`, `certifiedMass_eq`, `packingWeight_bounds`; `alphaCountQ`/`shellCorrQ`; computable `cmLo`/`cmHi`; **general** `certifiedMass_bounds` (`cmLo Z N d ≤ certifiedMass Z N ≤ cmHi Z N d`, any nucleus); regression `certifiedMass_c12` (`21875 < certifiedMass 6 6 < 21877 m_e`) | interval analysis (treated as analysis, not selection) | interval analysis (treated as analysis, not selection) |
| `NuclearRegime` | regime classification through the `Z=96`, `N=152` deformed frontier; `cm_at_frontier`, `cf_beyond_frontier` |
| `SingleParticle` | schematic `nlj` orbital sequence through `126` and `184`; `nuclearOrbitals126_occupation`, `nuclearOrbitals184_occupation`; schematic `orbitalEnergy`, `orbitalLevels`, `cumulativeEnergy`, `smoothEnergy`, `strutinskyCorrection`; `spinOrbit`, `nilssonEnergy`, `nilssonLevels`, `nilssonCumulative`, `nilssonCorrection` |
| `ShellSystem` | shell pillars: Capacity `2j+1` and the oscillator `2n+l` order (`orbital_capacity`, `oscillator_order`), the cumulative ladder carries the magic numbers (`closures_on_ladder`); Map `χ` is the closure boundary (`mapTerm_eq`); Protocol is the orbital successor (`protocol_deterministic`); Toll is emission (`shellEmissionWidth_eq_partialWidth`); Margin is the reference cone (`marginSpace_card = 343914`); `l2_ratio_forced` and `e8OrbitalOrder` for the recorded fine order with `κ = χ/Δ`; spacing `ℏω(A) = χ·m_p/(Δ·A^{1/3})` (`shellQuantum`, `shellQuantum_cube`, `shellQuantum_antitone`) — about 6% above `41 A^{-1/3}` MeV | the uniform-coupling reading of spin–orbit |
| `ShellGaps` | closures as gaps: with `κ = χ/Δ` the largest gaps are `20, 40, 70` (`shellSystem_gaps`, `shellSystem_oscillator_closures_dominate`); with `κ = 1/ν`, `μ = χ/σ` in the standard Nilsson form they are `2, 8, 20, 28, 50, 82, 126` (`nilssonE8_gaps`, `nilssonE8_spinOrbit_closures`); smooth reference is the plain oscillator (`ho_degeneracy`, `l2_shell_average`, `spinOrbit_trace_zero`); `1/ν` is one over the channel count and one sector's symmetries reach all `16` channels (`nilssonKappa_eq_channel`, `sector_orbit`); `μ = χ/σ` is the quark latency ratio (`nilssonMu_eq_latency`); α level formulas compared (`nilssonEnergy_inverts_shells`, `alpha_standard_gaps`) | the reading of spin–orbit as a uniform coupling over the sector's channels |
| `ShellMass` | `certifiedMassFull = certifiedMass + ℏω·(Strutinsky)` dependency edge with a rational enclosure; comparison only (the E8 shell term is 3–4× the ledger residual and uncorrelated, `RESIDUALS.md`) | not a published mass |
| `IsospinLedger` | closed form of the typed link binding `L(A)·(w + s(N−Z)/A)` (`packingBindingTyped_closed`), constant per-step change `2sL(A)/A` (`packingBindingTyped_step`): the link ledger is linear in `N−Z` | comparison with the stability valley (`RESIDUALS.md`) |
| `NuclearShells` | `e8ShellLadder`, `e8ShellOccupations` aliases; `nuclearMagic = [2,8,20,28,50,82,96,126,152,184]`, each closure proved as an E8 expression; `nuclearShellSizes = [2,6,12,8,22,32,14,30,26,32]` |
| `Shells` | `orbitalCapacity l = 2(2l+1)`, `shellCapacity n = 2n²`, `shell_capacities : 2,8,18,32` | spin-1/2, angular-momentum degeneracy |
| `Hydrogen` | `rydbergEV_bounds : 13.6056930–13.6056931 eV`; `bohrRadius_bounds : 0.5291772–0.5291773 Å`; `hydrogenLevel_ratio`; `ground_is_lowest` | electron rest energy and `ħc` as unit inputs; certified `α` |
| `ProtocolCandidates` | finite set cohorts (`candidateCohorts`), weak-partner filter (`candidateCohortsWeak`), least-cost selection | set version (multiplicity lost) |
| `ListCohorts` | multiplicity-preserving list cohorts; `charge3`/`listCharge3`, odd fermion parity, weak partner; `muon_list_mem`, `electron_list_not`, `electron_neutrino_list_not` | nuclear candidate set and E8 rates |
| `TransitionSelection` | `TransitionFamily`, `familyCost`; every nonempty candidate set has a least-cost family (`exists_least_cost`); `selectedFamily_min` and `selectedRate_le`; `selected_is_persistence_optimum` | the candidate set of substrate families |
| `PersistenceRate` | `RateSystem`, `totalRate`, `Persists` = total hazard zero, `not_persists_of_pos`, `MeanLife = 1/totalRate`; least-hazard selection (`exists_least_totalRate`, `selectedSystem_min`) | E8 channel rates |

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

Moved to [`PMHadrons/OVERVIEW.md`](../PMHadrons/OVERVIEW.md): the proton and neutron are the only
masses that use the full six-pillar ledger, and they are the template the nucleus ledger reuses
(`LinkWeights`).

## What is derived vs input

- Derived: nucleon charge/baryon from substrate channels; shell combinatorics;
  hydrogen readouts from `α`; nuclear conservation and selection structure;
  proton stability; allowed tree-level particle decays.
- Input: spin-1/2, one protocol per colour axis, the `ħc`/`m_e` unit conversions,
  and — crucially — the **nuclear binding/cost order and channel rates**.
- Compared, not matched: the stability valley above `A ≈ 56` (`IsospinLedger`; the ledger has no
  `(N−Z)²` restoring term), shell closures with `κ = χ/Δ` (`ShellGaps`).
- Not yet derived: nuclear lifetimes and numeric particle lifetimes (deferred).
- Readings (stated with their comparison, not theorems):
  - spin–orbit as a uniform coupling over the coordinate sector's `ν = 16` channels, strength
    `1/ν` (`ShellGaps.sector_orbit` proves the transitivity; the closures `2, 8, 20, 28, 50, 82,
    126` and O-17 `d` splitting `5.29` vs `5.08` MeV compare; N-15 `p` `3.32` vs `6.32`);
  - the `l²` ratio `μ = χ/σ`, the same ratio as the quark latency leak (`nilssonMu_eq_latency`);
    empirical Nilsson `μ` grows from `≈ 0` (`N ≤ 2`) to `≈ 0.6` (`N = 5`), E8 has one constant;
  - the shell spacing `ℏω(A) = χ·m_p/(Δ·A^{1/3})` has no `A^{-2/3}` term: 6% above
    `41 A^{-1/3}` MeV at all `A`, 24% above the two-term fit `45 A^{-1/3} − 25 A^{-2/3}` at `A = 16`.
