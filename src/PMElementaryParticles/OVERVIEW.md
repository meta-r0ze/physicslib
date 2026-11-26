# PMElementaryParticles — checked results

EP uses the E8 node machine to classify persistent programs and read their outputs.
It imports PMSubstrate, PMAction, PMConstants and PMKAutomaton. It does not import PMFlavor.
See [README](README.md), [open work](TODO.md), and [SCOPE](../../SCOPE.md#named-premises).

## Programs and pillars

`EPSpine.programs_card` counts 15 witness indices: three generations times five visible
classes. `ProgramClasses.visible_channels_card` counts 15 channel labels. These are
different index sets. Their unrestricted product with generations would have 45 elements;
it is not the program count. Full occupied-program closure remains open.

| Topic | Checked result | Lean entry point | Input still supplied |
| --- | --- | --- | --- |
| Machine | The ring step is reversible. The clock period is 43. | `PMKAutomaton.Interface`, `ClockRing` | Physical admission and timing; see the [machine contract](../PMKAutomaton/OVERVIEW.md#kautomaton-closeout). |
| Classes | Six label classes; five are visible to the substrate observables. | `ProgramClasses.classOf`, `visibleClasses_card`, `invisible_iff` | Physical readout interpretation. |
| Program | A program has a label, generation, reference, firing patterns and packet. | `EPSpine.Program`, `program_walk` | Its occupied region and execution. |
| Witness | Each visible class has a one-registration witness in every generation. | `EPLabelGen.spine_generations`, `EPSpine.programs_card` | Joint closure and physical footprint. |
| Label | Ring motion keeps label and generation. | `EPLabel.label_readout`, `EPLabel.spine_labelled` | Physical species assignment. |
| Checks | The three-site toy ring has finite survivor certificates. | `PMChecks.PMElementaryParticles.{Protocol,PillarPredicates,SurvivorClasses}` | The toy ring is a separate finite model. |

| Pillar | Condition on `ProgramWitness.RingProgram` | Entry point |
| --- | --- | --- |
| Capacity | At most two full rings of registrations per period. | `Capacity` |
| Map | The record differs from the reference; the class is visible. | `MapRecord`, `MapClass` |
| Protocol | The tick is reversible. | `RingReceiver.tick_bijective` |
| Governor | Some site does not fire. | `Governor` |
| Toll | Each differing ring registers at least once per period. | `Toll` |
| Margin | Each registering ring stays below 43 registrations. | `Margin` |

## Footprint: what the generation can change

| Family or test | Checked result | Lean entry point |
| --- | --- | --- |
| One preserving root step | Zero glue key keeps generation. A nonzero key changes it. Preserving both generation and internal content selects exactly the same 24 spacetime D4 roots for all labels and generations. | `FootprintNoGo.generation_preserved_iff`, `step_preserves_both_iff` |
| Common reachable-set functional | A common functional of relative displacements within a fixed step budget cannot distinguish generations or labels. Other program inputs are not removed. | `FootprintNoGo.footprint_functional_independent`, `event_footprint_functional_independent` |
| Requested two-root intermediate | A first hop with the starting glue key sends it to zero. That state cannot be a `Program`. EPLabel has no separate transient admission predicate. | `GluedExcursions.no_typed_intermediate`, `programCompatible_empty` |
| Raw label-restoring pairs | Before admission, every channel has 512 ordered pairs and 33 distinct spacetime displacements. Real span dimension is 4; spatial span dimension is 3. The full displacement sets differ across generations. | `restoring_counts`, `spacetime_span_dimension`, `spatial_span_dimension`, `displacement_sets_distinct` |
| Charge-conserving partner pairs | A nontrivial weak flip changes electric charge. Distinct charge-conserving colour partners have no two-root increment in the current doubled label code. | `weak_partner_charge_changes`, `partner_increments_disjoint`, `relabelPairs_empty` |

The table below concerns raw algebraic displacements. It asserts no admitted
execution. Zero displacement is separate from clock-only and spatial-only motion.
The spatial split is orthogonal to the existing clock covector in the aligned D4 metric.

| `genIndex` | Glue key | Distinct clock readings: count | Zero / clock-only / spatial-only / mixed |
| --- | --- | --- | --- |
| 0 | (0,1) | -2:1, -1:6, 0:19, +1:6, +2:1 | 1 / 2 / 18 / 12 |
| 1 | (1,0) | -1:10, 0:13, +1:10 | 1 / 0 / 12 / 20 |
| 2 | (1,1) | -1:10, 0:13, +1:10 | 1 / 0 / 12 / 20 |

No column gives the declared tier sets. There is no derived generation-to-tier map.
An empty typed-compatible pair family does not mean a zero physical footprint.
See [GluedExcursions](GluedExcursions.lean) for the 21 class/species rows, ordered-pair
histograms and the admission boundary. No count is identified with `Footprint.events`.

## Generation orbits

The existing Closure applications use the twelve slice-root reflections.
`GenerationOrbits.sliceGroup` packages exactly these generators. The two
`SliceHop` swaps are restrictions of them. This is not a classification of
all E8 automorphisms that fix the clock.

| Visible class | Species from CarrierChannels | Generation orbits | Declared tiers (`TierLedger.tiersFor`) |
| --- | --- | --- | --- |
| 0 | up | {0}, {1}, {2} | {0,2,3} |
| 0 | down | {0}, {1}, {2} | {0,1,2} |
| 1 | up | {0}, {1}, {2} | {0,2,3} |
| 2 | down | {0}, {1}, {2} | {0,1,2} |
| 3 | electron | {0}, {1}, {2} | {0,1,2} |
| 3 | neutrino | {0}, {1}, {2} | {0,1,2} |
| 5 | electron | {0}, {1}, {2} | {0,1,2} |

| Test | Checked result | Entry point in `GenerationOrbits` |
| --- | --- | --- |
| Key action | Every generator and group element keeps every glue key. The induced permutation group is the identity. | `group_preserves_key`, `generationAction_unique`, `generationAction_range` |
| Class restriction | Every generation's channel placement is fixed pointwise. Each class-respecting subgroup is the full cited group. | `group_fixes_channels`, `classGroup_eq_top`, `finite_orbit_table` |
| Program cost | An invariant cost is equal along a program orbit. No such orbit joins distinct generations. A real invariant function can separate them. | `invariant_cost_equal`, `sameProgramOrbit_generation`, `invariant_can_separate` |
| Excursions | Same-orbit 33-displacement sets have the identity image witness. Only index 0 has clock readings ±2. Every group element fixes that index. | `orbit_displacements_image`, `two_tick_generation`, `two_tick_generation_fixed` |

Indices use `EPLabelGen.genIndex`: 0 = (0,1), 1 = (1,0), 2 = (1,1).
No derived map assigns these indices to tier entries or to light/heavy species.
This group forces no cross-generation tie, so there is no forced tie to break.
The orbit structures do not explain the up-type tier difference.
SCOPE's prose Closure premise does not define an exhaustive clock stabilizer
or its action on programs. A claim about a larger group needs that definition
and a proof that it respects the existing labels. No new premise is added here.

## Charges

The canonical rule is `PMConstants.Hypercharge.electric`: `blAxis / 2 + t3Sign`.
The axis and sign are the carrier premises in SCOPE. A numerical charge table is
not an extra species input. Antiparticle charges reverse the species sign.

| Encoding | Charge source | Agreement result |
| --- | --- | --- |
| Packet | `ColourRouting.electric` calls the canonical rule on the carried packet. | `CarrierChannels.electric_transport` |
| EP channel | `CarrierChannels.electric` calls the same rule on its axis and sign. | `CarrierChannels.packet_charge_eq` concerns hypercharge, not electric charge. |
| Base protocol | `ProtocolInventory.BaseProtocol.charge` supplies axis and sign. | `ProtocolInventory.base_charge_values` checks the four outputs. |
| Species | `CarrierSpecies.charge` reads its base protocol. | `channelSpecies_charge` |
| Final state | `FinalStateBridge.DecaySpecies.charge` reads species and sign. | Charge conservation in `FinalStateBridge` and `SubstrateFinalStates`. |
| Channel ledger | `ChannelParticleLedger.channelCharge` reads the EP channel. | `channelCharge_eq_Q` |
| Carrier amplitude | `CarrierCouplings.amplitude` uses rational charge times `sqrt alpha`. | `neutrino_em_zero` |
| Charged W | `TopTransition.Boson.charge` uses the doublet charge difference. | The exact rational difference is one. |
| Electromagnetic coupling | `ChainCouplings.electromagneticCouplingSquared` is a squared coupling. | It is not a charge. |

## Mass via OccupancyCost

Fermion masses use one scalar reading: `PMSubstrate.OccupancyCost.cost`.
The canonical counts and residuals are in `PMSubstrate.SpeciesFootprints`.
The [single footprint table](../PMSubstrate/OVERVIEW.md#occupancy-footprints)
records their status. Counts are whole numbers. A residual records a term for which
no whole pillar count has been supplied. It is not evidence for a persistent region.

| Particle | Tier | Canonical footprint | Checked result | Open count |
| --- | --- | --- | --- | --- |
| Electron | Point | `OccupancyCost.Footprint` with `events := 1` | One event costs one electron unit. | Physical point-region identification. |
| Muon | Line | `SpeciesFootprints.Lepton.muonFootprint` | `LeptonMasses.muon_value`, feedback fixed point. | Sweep, attachment, residual and feedback rule. |
| Tau | Area | `SpeciesFootprints.Lepton.tauFootprint` | `LeptonMasses.tau_value` | Area attachment, multiplicity and inherited line. |
| Up, down | Point | `SpeciesFootprints.Quark.upFootprint`, `downFootprint` | `QuarkMasses.up_value`, `down_value` | Region, dilution and overhead. |
| Strange | Line | `SpeciesFootprints.Quark.strangeFootprint` | `QuarkMasses.strange_value` | Region, multiplicity and charges. |
| Charm, bottom | Area | `SpeciesFootprints.Quark.charmFootprint`, `bottomFootprint` | `QuarkMasses.charm_value`, `bottom_value` | Region, multiplicity and residuals. |
| Top | Volume | `SpeciesFootprints.Quark.topFootprint` | `QuarkMasses.top_value` | Region and fractional leading correction. |
| Neutrino | Declared tiers | No selected footprint. | `TierLedger.neutrinoTiers` checks the declared list. | Occupied region and output. |

`PersistencePremises.causal_cone_card` proves the square-region count. It does not
identify a species with that region. First derive region dimensions. Then check
`TierLedger.tiersFor`; only then compare masses. The physical unit, one clock event
costs one electron mass, is a named premise in SCOPE.

### Generations on the E8 wire

`KoideSplit` checks an algebraic norm split. `KoideSelection` uses a supplied
generation record. Neither result derives a species footprint or a Fourier phase.
See their module docstrings for excluded assignments and numerical checks.

## Record comparisons and heavy flip flag costs

| Topic | Lean modules | Checked result | Input still supplied |
| --- | --- | --- | --- |
| Exact record | `RecordCoordinates`, `RecordEncoding`, `RecordPortIdentification` | Finite coordinates and embedding identities. | Physical register identification. |
| Receiver trace | `IsolatedExcitation`, `IsolatedReceiverTrace`, `RingSurvivors` | Occupancy, registration counts and finite-ring bounds. | Initial requests and occupied traffic. |
| Writer | `HeavyFlipRecords`, `ElectricHeavyRecord`, `ElectricFourPortRecord` | Record writes and flag sums under the given guards. | Admitted pulse, seed and reuse. |
| Setup | `ElectricCompanionSetupFlagCosts`, `ElectricPrimitiveFlagCosts` | Primitive word and companion setup costs. | Physical availability of the bank. |
| Current | `ElectricChiralKick`, `ElectricCoordinateDecoder` | Conditional current and decoder words. | Timings and preparation. |
| Protocol flags | `ProtocolFlagCosts`, `WireReferenceCost` | Static constraints and factorized writer costs. | Sampling and reset contract. |
| Schedule | `WireSchedule` | Serial placement and costs including the supplied remainder. | Admission, traffic, reset and tariffs. |
| Insertion | `ChargedInsertion`, `GappedGluedCrossing` | Conditional operators and crossing identities. | A link from execution to occupied footprint. |

### Charged density and wall leakage

`PMAction.WallRestChirality` checks static density and readout identities. It does not select
an occupied trace. The `ExternalStates` docstring contains the comparison audit. The
`WireSchedule` and `PolarMeasure` docstrings hold schedule and continuum notes.

## Decay and widths

The shared survival and positive-rate mean-life API is `PersistenceMechanics.Rates`.
EP supplies physical adapters. Stable zero-rate configurations do not receive a
zero mean life from a reciprocal convention.

| Topic | Module or declaration | Checked result | Supplied input |
| --- | --- | --- | --- |
| Routing | `ProtocolDynamics`, `SubstrateFinalStates`, `FinalStateBridge` | Charge-conserving finite descent and final-state bridges. | Physical final-state choice. |
| Survival | `DecayLaw`, `Survival`, `MeanLife` | Finite-tick law and continuum relation; shared constant hazard. | Persistence premises and rate. |
| Finite channels | `RateModel`, `BetaLattice`, `LeptonLattice`, `LeptonLifetime` | Finite mode sums and positive-rate lifetimes. | Mode set, support and scale. |
| Weak vertex | `WExchangeRate`, `VATrace` | Contact limit and spin trace. | Physical current and flux identification. |
| Massless width | `MuonRate.muon_rate` | `G² m⁵ / (192 pi³)` from the contact amplitude and measure. | Contact interaction, external states and flux. |
| Massive width | `MassiveWidth.closed_width` | Exact daughter phase factor. | Physical daughter and parent assignment. |
| Measure | `PairSphere`, `PairTensor`, `PhaseSpace`, `PolarMeasure` | Angular, radial and energy-shell integrals. | Physical scale and support. |
| Muon tree | `MuonLifetime`, `PhysicalUnits` | E8 masses and canonical Fermi coupling give the tree width. | Fermi/VEV premises and SI unit anchors. |
| Muon correction | `MuonLifetimeCorrected`, `MuonQEDLoops`, `MuonLifetimeHigherOrder` | Certified intervals for supplied QED formulas. | QED coefficients and leptonic running law. |
| Tau scaling | `TauLifetime.tau_lifetime_tree` | Transports supplied muon-time and branch intervals. | Muon time and electronic branch. |
| Tau E8 | `TauE8.tauLifetimeE8_bounds` | Branch-conditional lifetime from E8 muon width. | Electronic branch. |
| Tau correction | `TauLifetimeCorrected.tau_lifetime_corrected` | Corrects the supplied tree interval by phase, W and QED factors. | Supplied correction formulas; E8 running at both scales. |
| Neutrino comparison | `NeutrinoContext` | Floor-scale enclosures and conditional exclusion tests. | Supplied comparison window; e8p instantiates it. |
| Tau branches | `TauBranching.phase_bounds`, `parton_level`, `supplied_needs` | Leptonic phase ratio and branch/hadronic-factor relation. | Inclusive hadronic factor. |

## Supplied inputs and premises

Measured values belong to `tools/e8p/E8PConstants/Experimental.lean`.
The reporter supplies the tau electronic branch and, for the scaled-muon row,
the measured muon time. The tau running coupling uses `MuonQEDLoops.runningAlpha`
at the E8 tau mass. It has no measured running-coupling anchor. This is the same
supplied leptonic running model used at the muon scale, not a complete threshold model.
The van Ritbergen–Stuart series is supplied theory, not a measurement or a PM derivation.

## EP premise ledger

Read the shared statements in [SCOPE, Named premises](../../SCOPE.md#named-premises).
The names in this table identify the rows by the Lean module in SCOPE's
“Where it enters in Lean” column. Local inputs below give the remaining
choice and the first layer that needs it.

| Layer | Lean location or SCOPE row | Status |
| --- | --- | --- |
| Substrate | SCOPE · `ClockAlignment` | Named placement premise. `alignedSectorBasis_eq` checks the explicit placement. |
| Substrate | SCOPE · Lorentzian signature and complex amplitudes | Named model premises. Root moments through degree four are PM theorems. |
| Substrate | `ChannelPlacement.channelE8`, `referenceClass_eq_clock` | Proved from PM. |
| Substrate | `PMConstants.Values.alpha`, `PMConstants.Values.fermi 1` | PM coupling and conversion formulas. The Fermi value inherits the SCOPE VEV structure. |
| Substrate | `SharedUnits.me`, `PhysicalUnits.electronTime` | PM conversion at the external SI unit anchors. |
| Node | SCOPE · `ClockSites`, `RingReceiver.tick` | Named tick-to-root identification. The finite clock and ring movement are checked. |
| Node | SCOPE · `ClockTickWeights`, `Machine.SliceHop` | Named closure premise. The discrete orbits are checked. |
| Node | SCOPE · `PMKAutomaton.Interface` | Named admission, geometry, resources, booking, traffic and tariff inputs. See the [upstream closeout](../PMKAutomaton/OVERVIEW.md#kautomaton-closeout). |
| Node | `CommonResponse.bookedCapacity` | PM sum rules. Local capacity values, distinct paid events and their common unit are supplied under SCOPE's machine-input row. |
| Carrier | SCOPE · `CarrierRepresentation`, triality to vector | Named carrier premise. |
| Carrier | SCOPE · `CarrierRepresentation`, sign index | Named carrier premise. |
| Carrier | SCOPE · `CarrierRepresentation`, reserved lepton axis | Named carrier premise. |
| Carrier | SCOPE · `Hypercharge`, `RequirementTable` | Named representation inventory with a sterile singlet. |
| Carrier | `CarrierRepresentation.carrierCharges_eq_standard` | Charge equality follows in Lean from the three carrier premises. The standard table is a comparison target for this result. |
| Carrier | SCOPE · `PacketGaugeActions` | Named weak `SU(2)` action on the sign pair. Colour and the hypercharge direction follow from PM under the carrier premises. |
| Carrier | SCOPE · `GeneratorNormalization` | Named stiffness normalization, inherited through the weak couplings. |
| Carrier | SCOPE · `LinkMass` | Named transport form. The link charge is derived. |
| Carrier | SCOPE · `HeavyFlipControl`, `ElectricCompanionBank`, `ElectricChiralKick` | Named heavy record and occupied companion contract. The typed guard action is proved. |
| Carrier | `VacuumLabel`, `refRecord`, `SharedReference`, `ColourReference` | Physical vacuum, sector and readout choice are open. |
| Carrier | `CompositeSchur` | Gapped crossing and flip coefficients are supplied. A booked execution must realize the coherent blocks. |
| Carrier | SCOPE · `ChargedInsertion`, `ResonanceLift` | Named offset and matched-port admission. Persistence of the calibration channel is open. |
| Carrier | `LinkGapLaw.gapA`, `LinkGapLaw.gapB` | Supplied alternatives for matching `yv` to detuning. The `κ_τ` measurement is an e8p comparison. |
| Protocol | SCOPE · `WireSchedule.Premises` | Named serial route and admitted bookings. |
| Protocol | SCOPE · `WireReferenceCost`, `PMKAutomaton.Values` | Named population and reset contract. The threshold arithmetic is proved. |
| Protocol | `EPSpine.spine`, `EPSpine.witnessAt_registrations` | Proved for class witnesses. Closure of a complete occupied program is open. |
| Protocol | SCOPE · `TierLedger.tiersFor` | Named tier lists. The wire address assignment remains an explicit input. |
| Protocol | `LeptonMasses.muon`, `LeptonMasses.tau` | Canonical species footprints with supplied counts. The invariant values and arithmetic follow from PM. |
| Protocol | `QuarkMasses.up` through `QuarkMasses.top` | Canonical species footprints with supplied counts. The invariant values and arithmetic follow from PM. |
| Protocol | `KoideSelection.generationLaw` | Named local generation-record premise. Koide follows with selection on that law. |
| Protocol | `KoideSplit.circulant_koide` | The split is proved for supplied amplitudes. Phase and relation to an occupied trace are open. |
| Protocol | SCOPE · `ExternalStates`, `NativeExternal` | Named physical species and decay/current readout. |
| Protocol | `CarrierAmplitude`, `CarrierTransitionOperator` | Supplied coupling assignment and link from the operator to physical external states. |
| Protocol | `ProtocolDynamics`, `RateModel` | Decay relation and finite accounting are proved. Physical histories and their event rates are supplied. |
| Protocol | `MuonRate.parentFlux`, `WExchangeRate` | Supplied relativistic flux and physical V−A/weak contact identification. The kinematic and zero-transfer formulas are proved. |
| Protocol | `PolarMeasure`, `PairSphere`, `LeptonLattice` | Measures and finite counting are proved. The support and scale choice for the physical final state are supplied. |
| Protocol | SCOPE · `HazardForm`, `MeanLife` | Named persistence-law inputs. |
| Protocol | SCOPE · Born rule and `InclusiveMixing` | Named probability interpretation where amplitude-derived channel weights are used. |
| Protocol | `MuonLifetimeCorrected`, `MuonQEDLoops` | SM QED coefficients and correction expansion supplied. |
| Protocol | `TauLifetime.tauLife`, `TauE8.tauLifetimeE8` | Experimental muon lifetime and branching fraction for the first. Experimental branching fraction for the second. |
| Protocol | `TauLifetimeCorrected.qedTau` | Supplied QED formula. `MuonQEDLoops.runningAlpha tau` uses the E8 baseline coupling. |
| Protocol | `TauLifetimeCorrected.wRatio` | SM finite-propagator correction applied with the E8 W mass. |

## Verification

Use `./build.sh fast <module>` for changed artifacts, `./build.sh lean <module>`
for typechecks, and `./build.sh audit` for axioms and dependency direction.
Build reporter checks with `./build.sh e8p`. The three-site certificates live in PMChecks.
