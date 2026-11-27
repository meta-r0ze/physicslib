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
| Margin | Each differing bit ring stays below 43 registrations. | `Margin` |

## Program dimension

Occupancy counts held events. Registration counts traffic through a receiver. Erasure
counts discarded information. These counts are different. The joint-successor resource
work is parked for decay. It does not select an occupancy footprint.

| Question | Checked result | Entry point | Limit |
| --- | --- | --- | --- |
| Ring bound | Every program has at most 86 registrations in 43 ticks, even without the pillars. | `SpacetimeProgram.program_registration_bound` | A held-event bound needs the bridge in `footprint_bound`. |
| Margin | Each differing bit ring has at most 42 registrations. A two-bit line has at most 84 relevant registrations. | `relevant_margin_bound`, `relevant_one_bit_bound` | The bound 42 per spatial line needs Hamming distance one. Margin does not constrain equal bit rings. |
| Packing | If each line has bound c and the required total is R, at least ceiling(R/c) lines are needed. | `required_lines` | Use c = 84 generally, or 42 with the one-bit hypothesis. This is a lower bound, not an attainable packing. |
| Ring family | Capacity sums over a finite family. Toll, Margin, Map and Governor hold per line. A singleton family is equivalent to the old program data. | `family_capacity`, `family_toll`, `family_margin`, `family_map_governor`, `singletonFamilyEquiv`, `singleton_pillars` | No spatial interaction or root execution is inferred from a family. Independent line ticks are reversible (`family_protocol`). |
| Root execution | Each step is one of the 24 aligned spacetime roots. Every step changes space. | `RootExecution`, `execution_changes_space`, `no_fixed_spatial_root` | A fixed spatial clock line cannot contain even one such step. The requested geometric one-line reduction is therefore unavailable. |
| Reachability | A finite recursion enumerates exact root-word endpoints. | `rootReachableFinset`, `mem_rootReachableFinset`, `directionRoots` | Reachable alternatives are not simultaneously held events. Event index and lattice clock coordinate must remain distinct. |
| Required R | Every generation and visible channel has a pillar witness with one relevant registration. | `relevant_floor`, `one_relevant_in_every_generation` | There is no derived species-dependent requirement R. The two-bit record and excursions do not supply one. |

These are the declared integer event fields in `SpeciesFootprints`, not scalar mass values.
The arithmetic is certified by `SpacetimeProgram.declared_event_counts`.

| Species | Declared leading term | Event field | Exceeds 86? |
| --- | --- | ---: | --- |
| Up | D / η | 4 | No |
| Down | D / η; the σ term stays in the residual | 4 | No |
| Muon | σΔ | 215 | Yes |
| Strange | DΔ / η | 173 | Yes |
| Tau | χΔ² − σΔ | 3483 | Yes |
| Charm | DΔ² / (η(σ−χ)) | 2479 | Yes |
| Bottom | DΔ² / η | 7439 | Yes |
| Top | Δ³(D+1/D) | 337904 | Yes |

The current single-program registration account cannot hold the six larger event fields.
This statement uses registrations as the account. No theorem equates all physical held
events with those registrations. The electron unit is separate; neutrinos have no declared
footprint in `SpeciesFootprints`.

| Spatial directions | Full speed-one box cone, 0 ≤ t < 43 | Envelope leading power | Declared leading powers to compare | Allowed roots within that subspace | Exact one-event endpoints |
| ---: | ---: | --- | --- | ---: | ---: |
| 0 | 43 | Δ | Muon σΔ; strange DΔ/η | 0 | 0 |
| 1 | 1849 | Δ² | Tau χΔ²−σΔ; charm and bottom area terms | 4 | 4 |
| 2 | 105995 | Δ³ | Top Δ³(D+1/D) | 12 | 12 |
| 3 | 6835753 | Δ⁴ | No declared quartic species term | 24 | 24 |

`box_one` reuses `PersistencePremises.causal_cone_card`; `box_counts` checks the sums.
The multidirectional box uses componentwise |x_i| ≤ t. Its tick index is not a root's
lattice clock coordinate. No exact 43-step root-region minimum, occupied multiplicity
or species assignment is inferred. See `SpacetimeProgram` for the finite root enumerator.

## Mass as reversals per period

`ReversalEvents` proves the Boolean ring identity for arbitrary patterns and both guards.
A registration swaps streams in either direction. Direction stays fixed between registrations.
This counts realized events. `PhaseToRecord.expected_receiver_flag` computes a coherent
weight `DiagonalReadout.flag x`; it supplies no generation-to-phase encoding.

| Result | Entry point | Scope |
| --- | --- | --- |
| Registrations equal reversals at every finite horizon. | `registrations_eq_reversals`, `registration_iff_opposite_direction`, `direction_between_registrations` | One localized packet on either stream. |
| The reversal footprint has unit-price events and no extra terms. | `footprint`, `footprint_events`, `footprint_cost`, `footprint_ceiling` | A defined reading; identifying all physical held events with these reversals remains open. |
| The old witness has two total reversals and one differing-bit subtotal. | `RetainedMap.old_witness_two`, `ProgramWitness.witness_total` | Equal-ring traffic cannot be dropped from the total. |
| Keeping the equal bit ring quiet attains one total reversal in each generation and visible class. | `quietEqualRing`, `RetainedMap.current_minimum`, `quiet_program_cost` | Current pillars only. Its unit cost uses `OccupancyCost.cost_oneEvent`; it is not identified with the electron. |
| Every ring-root word preserves generation and internal content; the placed label reads back unchanged. | `RetainedMap.program_identity_conserved`, `word_label_readout`, `word_label_unique` | Any choice of clock-axis roots, including direction changes. |
| The label record cannot decode generation. | `label_record_cannot_decode_generation` | It still carries conserved label information. |
| A shared reader must recover the retained identity at every positive period end. | `ReadableReference`, `StrongMap`, `readable_generation`, `readable_class_record`, `readable_internal` | Generation, channel and conserved internal content. All retained ring fields are available; no free carrier tag is appended. |
| The quietProgram family has identical histories across generations for a common channel and site. | `quiet_observations_equal`, `no_uniform_quiet_decoder` | Even their complete ring states coincide. Other encodings are not excluded. |

Map is a decoding specification. `GenerationReadoutContact.coded_strong` supplies a shared
reader for preloaded requests as a countermodel; no physical preparation or coupling is inferred.

Historical context only: [Kac (1974)](https://www.cs.fsu.edu/~mascagni/Kac_1974_Rocky_Mountain_J_Math.pdf) studies the telegraph process.
[Gaveau–Jacobson–Kac–Schulman (1984)](https://doi.org/10.1103/PhysRevLett.53.419) relate it to the Dirac equation by analytic continuation.
This analogy supplies no premise, Dirac limit, conversion factor or stochastic rate here.

## Generation readout needs vacuum contact: audit

The present predicates allow information to be preloaded and retained without changing the glue key. No physical code is selected.

| Test | Checked finding | Entry point in `GenerationReadoutContact` |
| --- | --- | --- |
| General no-reader theorem | Equal native initial states cannot decode different generations. Zero-key words alone do not imply equal initial states. | `no_reader_equal_initial_states`, `zero_key_word_preserves` |
| Preloaded reader | A shared native-request reader meets StrongMap for all three generations, with one reversal. This is a countermodel, not a physical derivation. | `code_retained`, `preloaded_strong_family`, `coded_minimum`, `readable_with_zero_key_word` |
| Nonzero roots | k→k+h→k avoids zero when nonzero h differs from k. The h=k choice in GluedExcursions is a restriction. | `other_key_avoids_zero`, `returning_pair_avoids_zero` |
| Ring reversal | A one-tick stream turn has a compatible single zero-key clock-root position increment. No timed pair factorization follows. | `zero_key_turn_at_site`, `one_event_is_not_two` |
| Intermediate | A cancelling first hop leaves the placed label vector. A zero-key vector is not a typed EP program; no native-vacuum identification is given. | `cancelling_first_hop`, `zero_key_not_a_program`, `native_admission_iff` |

There are 512 raw label-restoring pairs and 33 displacements per generation, with no native reversal action.
Typed-compatible pairs are empty. The clock histograms count ordered pairs, not displacements.

| Glue key | Raw signed clock reading : ordered-pair count | Word length |
| --- | --- | ---: |
| (0,1) | −2:8, −1:96, 0:304, +1:96, +2:8 | 2 |
| (1,0) | −1:128, 0:256, +1:128 | 2 |
| (1,1) | −1:128, 0:256, +1:128 | 2 |

`GluedExcursions.{restoring_counts,ordered_pair_clocks,programCompatible_empty}` certify these rows.
Word length is two; the signed residue in ZMod 43 is not elapsed time. Native contact timing is not derived.

| Glue key | Class | Species | Vacuum-contact reversal words | Ticks/contact | Least contact reversals/period | Declared tiers |
| --- | ---: | --- | --- | --- | --- | --- |
| (0,1) | 0 | up | Not defined | Not derived | Admission stop | {0,2,3}; unassigned |
| (0,1) | 0 | down | Not defined | Not derived | Admission stop | {0,1,2}; unassigned |
| (0,1) | 1 | up | Not defined | Not derived | Admission stop | {0,2,3}; unassigned |
| (0,1) | 2 | down | Not defined | Not derived | Admission stop | {0,1,2}; unassigned |
| (0,1) | 3 | neutrino | Not defined | Not derived | Admission stop | {0,1,2}; unassigned |
| (0,1) | 3 | charged lepton | Not defined | Not derived | Admission stop | {0,1,2}; unassigned |
| (0,1) | 5 | charged lepton | Not defined | Not derived | Admission stop | {0,1,2}; unassigned |
| (1,0) | 0 | up | Not defined | Not derived | Admission stop | {0,2,3}; unassigned |
| (1,0) | 0 | down | Not defined | Not derived | Admission stop | {0,1,2}; unassigned |
| (1,0) | 1 | up | Not defined | Not derived | Admission stop | {0,2,3}; unassigned |
| (1,0) | 2 | down | Not defined | Not derived | Admission stop | {0,1,2}; unassigned |
| (1,0) | 3 | neutrino | Not defined | Not derived | Admission stop | {0,1,2}; unassigned |
| (1,0) | 3 | charged lepton | Not defined | Not derived | Admission stop | {0,1,2}; unassigned |
| (1,0) | 5 | charged lepton | Not defined | Not derived | Admission stop | {0,1,2}; unassigned |
| (1,1) | 0 | up | Not defined | Not derived | Admission stop | {0,2,3}; unassigned |
| (1,1) | 0 | down | Not defined | Not derived | Admission stop | {0,1,2}; unassigned |
| (1,1) | 1 | up | Not defined | Not derived | Admission stop | {0,2,3}; unassigned |
| (1,1) | 2 | down | Not defined | Not derived | Admission stop | {0,1,2}; unassigned |
| (1,1) | 3 | neutrino | Not defined | Not derived | Admission stop | {0,1,2}; unassigned |
| (1,1) | 3 | charged lepton | Not defined | Not derived | Admission stop | {0,1,2}; unassigned |
| (1,1) | 5 | charged lepton | Not defined | Not derived | Admission stop | {0,1,2}; unassigned |

Native admission recognizes a supplied label in each bank; it does not identify ClockRing.V with a stationary mode.
The [first TODO](TODO.md#zero-key-intermediate-admission) is that missing operational admission/representation relation.
Item 4 stops here. These rows cover all visible groups; no physical ordering or tier assignment follows.

## Persistence of an isolated excitation

The closed resource-exchanging execution is parked for decay. It does not define the
held-event mass reading. `ExcitationPersistence` and `JointSuccessorConstraints` state
the missing contracts. Their module docstrings keep the detailed audit.

| Part | Checked result | Open contract |
| --- | --- | --- |
| Vacuum | Distinct rest modes are stationary (`ExcitationPersistence.distinct_stationary_modes`). | Admit their occupied interaction and return. |
| Receiver | Localized Boolean occupancy is conserved. The embedding ignores its vacuum argument. | Derive requests from the occupied background. |
| Joint tick | Reversible packet lifts project to a supplied core. | Identify joint resources, locality and the admitted packet operation. |
| Reference supply | Loaded seeds and a clean backward stream give conditional restoration. | Derive and renew that supply within the execution. |
| Closed period | Zero erasure does not prove reference renewal. Ring return needs the stated port/two-clock hypotheses. | Close the admitted period; see `RingReceiver.ring_return_of_ports`. |

See the [machine TODO](../PMKAutomaton/TODO.md#reachable-occupied-background).
Coset-0 contacts and full-state persistence remain open. A one-reversal count is not a
full-state return theorem. No electron identification or mass comparison follows.

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

`PMKAutomaton.ClockSymmetry.Gplus` is the full subgroup of W(E8) that keeps
both aligned D4 factors and fixes `ClockPlane.cu`. `Gpm` permits its negative.
The root-reflection words generate these intrinsic groups. This does not
replace the 43-state clock reading, which also uses `cv`.

| Group before label restriction | Image on generation keys | Generation orbits | Entry point |
| --- | --- | --- | --- |
| G₊: `cu` fixed | Identity and the swap 1↔2. Key (0,1) is fixed. | {0}, {1,2} | `ClockSymmetry.full_generation_image`, `positive_generators_exhaustive` |
| G±: `cu` fixed up to sign | The same two permutations. | {0}, {1,2} | `full_generation_image`, `line_generators_exhaustive` |
| Both factor discriminants | The same permutation acts on both. Fixing `cu` fixes its vector class. | No third permutation occurs. | `sector_annihilator`, `keyAction_descent`, `diagonal_glue`, `fixes_clock_key` |

The existing placement supplies more structure. Each class lies on one wall.
Its generation cycle is oriented. A glue transposition reverses that cycle
and exchanges the wall classes. It cannot preserve any one visible class.
The result holds for every element of the full groups, not just one witness.

| Visible class | Carrier species | Label-respecting G₊ orbits | Label-respecting G± orbits | Raw swap and its label obstruction | Declared tiers |
| --- | --- | --- | --- | --- | --- |
| 0 | up | {0}, {1}, {2} | {0}, {1}, {2} | Spatial-axis flip + internal clock-adapted axis flip; changes wall class. | {0,2,3} |
| 0 | down | {0}, {1}, {2} | {0}, {1}, {2} | Same obstruction. | {0,1,2} |
| 1 | up | {0}, {1}, {2} | {0}, {1}, {2} | Same obstruction. | {0,2,3} |
| 2 | down | {0}, {1}, {2} | {0}, {1}, {2} | Same obstruction. | {0,1,2} |
| 3 | electron | {0}, {1}, {2} | {0}, {1}, {2} | Same obstruction. | {0,1,2} |
| 3 | neutrino | {0}, {1}, {2} | {0}, {1}, {2} | Same obstruction. | {0,1,2} |
| 5 | electron | {0}, {1}, {2} | {0}, {1}, {2} | Same obstruction. | {0,1,2} |

| Test | Checked result | Lean entry point |
| --- | --- | --- |
| Class and species | No class-respecting element swaps generations. A species refinement cannot restore a rejected element. | `FullGenerationOrbits.classGroup_generation_identity`, `sameOrbit_iff`, `species_generation_identity` |
| Program cost | The typed class-program action obeys the group laws. An invariant cost is equal along its orbits. An invariant real function may separate distinct generations. | `programAction_one`, `programAction_mul`, `invariant_cost_equal`, `invariant_can_separate` |
| Spatial orientation | The raw swap has representatives with spatial determinant -1 and +1. Thus the glue swap is not a test of chirality. | `ClockSymmetry.swap_orientations`, `swap_generation_check`, `even_swap_generation` |
| Carrier axis | Flipping the original lepton axis or any original colour axis fails to fix the internal clock projection, even up to sign. The adapted swap is not a carrier doublet-index flip. | `FullGenerationOrbits.carrier_axis_clock_checks`, `no_single_carrier_axis` |
| Excursions | The fixed key is index 0, the key with raw ±2 excursions. | `fixed_excursion_key` |
| Clock boundary | The explicit swap changes the full 43-state reading. Its use as a symmetry of an execution cost remains conditional. | `ClockSymmetry.swap_changes_clockReading` |

Indices use `EPLabelGen.genIndex`: 0 = (0,1), 1 = (1,0), 2 = (1,1).
No derived map assigns these indices to tier entries or to light/heavy species.
There is no forced cross-generation cost tie after the existing class placement.
A light-generation splitting is not forced to use a parity-odd structure.
Lepton-axis versus colour-axis flips do not explain the up-type tier difference.
No parity-odd named premise follows from this computation. Physical selection
of the oriented placement and the clock data of an execution remain open.
See [FullGenerationOrbits](FullGenerationOrbits.lean) for the scope of the cost action.

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
