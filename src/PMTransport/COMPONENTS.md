# PMTransport components

This is an inventory of the lattice-node model. Each node has retained
registers, local controls and a receiver. The encoded line and rings use
a common clock, the same rule at each site and two directed streams.
The packet has 16 slots. The boundary can account for erasure of a booked
export, separately from the reversible internal step. The Boolean line
and ring states and the 16-slot carrier are separate encodings. Their
joint physical update is open.

The [premise ledger](PREMISES.md) owns the physical questions. This page
locates them at component interfaces. [Machine](Machine/OVERVIEW.md)
indexes the implementation and its continuum applications.
[Interface](Interface.lean) and [Values](Values.lean) remain the certified
Transport entry points. [Components](Components.lean) packages the
pillar certificates with explicit hypotheses for unresolved inputs. No experimental data enters this inventory.

## Components

Unqualified module names refer to the files in Machine, PMTransport,
PMAction, PMConstants or EP. In the tables, a bare theorem name in a cell
shares the namespace of the preceding theorem in that cell.

| ID | Component | Modules | Certified operation or representation |
| --- | --- | --- | --- |
| C | Clock | `ClockPeriod`, `ClockDynamics`, `ClockControlledRoot`, `CarrierReferenceCycle`, `ClockedRootTrials`, `RootClockCalibration` | One phase register in the clocked models. `CarrierReferenceCycle.clock_closes` closes the cycle. `ClockedRootTrials.iterate_controls` advances the phase and retains the requests. |
| N | Node registers | `IndependentRegisters`, `RegisterSplit`, `RegisterPrograms`, `RegisterInteraction`, `RegisterVacuum`, `RegisterHamiltonian`, `RegisterControl`, `TwoSiteHandoff` | `IndependentRegisters.sectorEquiv` encodes two banks. `RegisterControl.occupation_conserved` preserves their occupation. The live and record streams are distinct. |
| G | Controller | `LocalController`, `RingReceiver`, `ClockedRootTrials`, `BranchPulseContract`, `NativePacketUpdate` | `LocalController.radius_one` reads the local retained controls and two incoming stream ports. `reversible_iff_rows` and `enumerated_rule_count` concern that retained table. `RingReceiver.tick_bijective` certifies the encoded rings. |
| P | Root and selector pulses | `RootTransfer`, `RootTransferPhase`, `RootTransferAccounting`, `RootBranchEncoding`, `RootPulseEvents`, `ActualRootRepair`, `RootOrderComparison`, `CarrierRootGate`, `CompletedCarrierPhase`, `ClassBlindFlip`, `SplitClassBlindFlip`, `SelectiveCarrierRouting` | `RootTransferPhase.quarter_pulse` and `half_pulse` specify primitives. `BranchPulseContract.program_correct` gives a comparison word. Short and long certain words have different serial bounds. |
| X | Receiver | `TwoSiteHandoff`, `OpenHandoff`, `LocalController`, `RingReceiver` | `TwoSiteHandoff.step_trace` gives ordered output ports. `LocalController.guard_outputs_eq_iff` separates equal requests or arrivals from the mixed unequal case. |
| L | Links | `NativePacketLinks`, `NativeCoherentLinks`, `NativePacketRouting`, `NativeLocalityBoundary`, `AxisHop`, `SliceHop`, `EdgeLocality`, `FiniteConfigurationControls`, `OpenReferenceFlow`, `HandoffAdmittance`, `ReferenceNode` | `OpenHandoff.address_step` and `OpenReferenceFlow.exchange_reflects`/`bypass_transmits` specify the line and streams. `HandoffAdmittance.through_eq_conductance` uses the two-stream current premise. `FiniteConfigurationControls.d4_configuration_realized` realizes supplied link controls. |
| M | Carrier and payload | `CarrierEvents`, `CarrierVacuumSector`, `CarrierVacuumEvolution`, `CarrierParity`, `CarrierWeyl`, `CarrierClifford`, `VectorEvenFrame`, `CarrierTriality`, `NativeCarrierState`, `NativeCarrierProtocol`, `GluedRegister`, `GenerationWalls`, `PacketGaugeActions` | `CarrierVacuumSector.range_iff_odd` identifies the odd sector and `VectorEvenFrame.range_iff_even` the even frame. `GluedRegister.crossing_word_glued` preserves the glued encoding through the crossing. `PacketGaugeActions.channel_index_bijective` indexes the packet. |
| R | Reference and preparation | `RootReferencePreparation`, `ReferenceSourceBoundary`, `OddReferenceSource`, `NativeReferenceBackground`, `RegisterReference`, `CoherentPreparation`, `SharedReference`, `ColourReference`, `ReferenceClassHop`, `ReferenceEconomy` | `NativeReferenceBackground.stationary_iff` classifies backgrounds in its supplied update. `OddReferenceSource.rest_modes_distinct` and `load_rest_mode` give distinct seeds and a loader. |
| D | Readout and flag account | `CarrierReadoutQuotient`, `CarrierResponse`, `CarrierProbe`, `MatchedLatticeProbe`, `ReadoutGateBoundary`, `ParityReadoutCircuit`, `InBandRootReadout`, `ScheduledReadout`, `InterferenceReadout`, `DiagonalReadout`, `NetCost`, `TollAmplitude` | `DiagonalReadout.state_flag` computes the weighted phase flag. `NetCost.expected_count_linear` adds expected registrations under its measure. `TollAmplitude.wireAmplitude_eq` evaluates survival amplitude for a supplied Toll. |
| F | Record path | `CoherentGate`, `CoherentRecordRestoration`, `RecordTransport`, `WalkRecordTransport`, `WalkReferenceCoupling`, `WalkReferenceProtocol`, `WalkReferenceCycle`, `RecordSupply`, `RecordFeedbackBoundary`, `PrimitiveRecordBoundary` | `CoherentGate.unequal_needs_orthogonal` distinguishes unequal writes. `RecordTransport.tick_fifo` moves records and `OpenHandoff.sum_exported` preserves exported population. |
| B | Boundary and sink | `BoundaryErasure`, `OpenHandoff`, `NativeLocalityBoundary`, `HomogeneousRouting` | `BoundaryErasure.identity_bijective` concerns protected registers. `erasing_pays_one` concerns a booked exported bit. `ring_cycle_erasure` is zero in the retained ring. |
| A | Maintenance and job coordination | `RefreshSchedule`, `CoherentRefresh`, `ReferenceMaintenance`, `RootMaintenance`, `FactorRepair`, `PersistenceSelection` | `RootMaintenance.event_is_root` realizes the given job. `CoherentRefresh.minimum_once` gives the once-per-item optimum at positive prices. `PersistenceSelection.within_family_iff_cheapest` compares supplied candidates. |
| E | EP writer and insertion endpoint | `HeavyFlipControl`, `HeavyFlipRecords`, `ElectricHeavyRecord`, `ElectricCompanionBank`, `ElectricCompanionSetupToll`, `ChargedInsertion`, `EventRequirements`, `WireSchedule`, `WireReferenceCost` | `ElectricHeavyRecord.root_writer` and `ChargedInsertion.joint_selector` give conditional operations. This is a downstream endpoint. The Transport scaffold carries only its upstream contracts. |
The control profiles, root-word encoders and continuum limits are link
implementations and analyses. `ConstantControls`, `ProfileControls`,
`FiniteRootWordControls`, `ConfigurationControls`, `D4EdgeSeparation`,
`NativeConsistency`, `CompactLimits` and `MatterContinuum` cover supplied
controls and their limits. They add no runtime ports to the discrete
machine. The preparation variants, companion bank, parity probe, FIFO
and feedback are included in their owning components above.

## Engineering checklist

| Check | Status | Scope |
| --- | --- | --- |
| Arbiter for contending visits | Missing · J | `RefreshSchedule.minimal_is_ledger` and `CoherentRefresh.minimum_once` certify a schedule for a supplied required set and prices. No joint arbitration on a common clock is supplied. |
| Ground or shared reference | Defined in Lean | `SharedReference.shared` identifies the reserved cell for the weak and hypercharge layout. `ColourReference.colour_reference_in_payload` locates its separate reference. Writer sharing at the same state and time is open · J. |
| Termination and sink | Defined in Lean for candidates · B | `OpenHandoff.export_trace`, `RecordSupply.ring_returns` and `BoundaryErasure.deliver` specify different endpoints. The admitted export and disposition are missing. |
| Power-on state | Defined in Lean for candidates · O | `RegisterVacuum`, `CarrierVacuumSector.range_iff_odd` and `NativeReferenceBackground.stationary_iff` constrain starts. The accessible occupied family is missing. |
| Fan-out to readers | Missing · W | The routed-value port, retained record port and comparison flag are typed separately. The EP attachment is open. The prose in [DOWNSTREAM](DOWNSTREAM.md#export-contract-requirement) describes its required inputs. |
| Per-part energy budget | Missing · K | `CarrierEvents.uniform_activation`, `OpenHandoff.balanced_basis_repair_flag` and `BoundaryErasure.erasing_pays_one` give exact accounts in their scopes. No exhaustive assignment of paid work to the parts exists. |

None of the physical interfaces in this checklist has a complete contract
only in Markdown. The premise documents describe open choices.

## Pillars

The column names follow [the PM pillar definitions](../PersistenceMechanics/Requirements.lean).
A theorem in a cell is a local certificate within its original hypotheses,
with a gap ID if additional physical data would be needed. A certificate
here can be a count, bound or rule instance. It does not allocate a
component's share of the substrate index. **Global only** means the
substrate result has no component allocation here. A global-only or
missing entry has a gap ID. For the substrate totals see
[PMSubstrate's impedance ledger](../PMSubstrate/OVERVIEW.md).

| Component | Capacity | Margin | Map | Protocol | Toll | Governor |
| --- | --- | --- | --- | --- | --- | --- |
| Clock | `Values.Delta_eq` | missing · T | `CarrierReferenceCycle.clock_closes` | `ClockedRootTrials.quiet_trial_tick` | global only · T | missing · T |
| Node registers | `TwoSiteHandoff.port_count` | missing · O | `RegisterControl.occupation_conserved` | `IndependentRegisters.occupied_encode` | global only · K | missing · G |
| Controller | `LocalController.enumerated_rule_count` | global only · O | `LocalController.reversible_iff_rows` | `LocalController.radius_one` | missing · K | missing · G |
| Root and selector pulses | `CarrierEvents.active_card` | `RootTransferPhase.quarterTime_positive` | `RootTransferPhase.phase_unitary` | `BranchPulseContract.program_correct` | `CarrierEvents.uniform_activation` · K | missing · G |
| Receiver | `TwoSiteHandoff.port_count` | missing · Q | `TwoSiteHandoff.exchange_four_returns` | `LocalController.receiver_realisation` | `RingReceiver.mixed_ring_flags` · K | missing · G |
| Links | missing · L | missing · L | `OpenHandoff.address_step` | `OpenReferenceFlow.bypass_transmits` | `HandoffAdmittance.node_current` · K | missing · G |
| Carrier and payload | `CarrierEvents.carrier_card`, `PacketGaugeActions.channel_index_bijective` | missing · O | `CarrierEvents.reflection_involutive` | `GenerationWalls.one_class_per_wall` | global only · K | missing · G |
| Reference and preparation | `SharedReference.reserved_single` | `OddReferenceSource.odd_reference_population` · Q | `SharedReference.shared` | `OpenHandoff.acceptance_iff_supply` | missing · K | missing · Q |
| Readout and flag account | missing · D | `DiagonalReadout.flag_bounds` | `DiagonalReadout.state_flag` | `BranchPulseContract.program_correct` | `TollAmplitude.wireAmplitude_sq` · K | missing · D |
| Record path | `RecordTransport.history_memory_bound` | missing · Q | `RecordTransport.stream_conserved` | `OpenHandoff.sum_exported` | missing · K | missing · W |
| Boundary and sink | `BoundaryErasure.disposition_count` | missing · B | `BoundaryErasure.identity_bijective` | `BoundaryErasure.erased_bit_merges` | `BoundaryErasure.erasing_pays_one` | missing · B |
| Maintenance and job coordination | missing · J | global only · J | `RootMaintenance.event_is_root` | `RefreshSchedule.minimal_is_ledger` | missing · K | missing · J |
| EP writer and insertion endpoint | `PacketGaugeActions.channel_index_bijective` | missing · O | `GenerationWalls.one_class_per_wall` | missing · W | `Values.outputFlagThreshold_eq`, `Values.balancedResetThreshold_eq` · K | missing · U |

## Interactions

Read from producer (row) to operation or consumer (column). The clock
and state-slot constraints count as interactions. A diagonal entry is a
local law. Theorems specify the certified part of a connection. Gap IDs
after a theorem identify its remaining input. Cells marked
**unspecified · E0** have no direct connection in the inventoried typed
operations. Their scope is explained below. A return trip through another
component appears in that component's row.

| From / to | C | N | G | P | X | L | M | R | D | F | B | A | E |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| C | `CarrierReferenceCycle.clock_closes` | `ClockedRootTrials.iterate_controls` | `ClockedRootTrials.ticks_zero_one` / `ticks_one_two` | `ClockControlledRoot.norm_preserved` · T | unspecified · G | unspecified · T | unspecified · E0 | `CarrierReferenceCycle.reference_encoded` | `RootClockCalibration.trial_weight` · T | unspecified · T | `BoundaryErasure.policy_cycle_counts_booked_exports` | unspecified · T | unspecified · T |
| N | `ClockedRootTrials.iterate_controls` | `RegisterControl.occupation_conserved` | `LocalController.radius_one` · O | `RegisterControl.extend_encode` | `LocalController.receiver_realisation` [live, record] | `TwoSiteHandoff.step_trace` [live, record] | `IndependentRegisters.sectorEquiv` | `RegisterVacuum.evolution_readout`, `NativeReferenceBackground.stationary_iff` · O | `InterferenceReadout.flag_bounds` · D | `RecordTransport.tick_fifo` [record] | `BoundaryErasure.identity_bijective` [retained] | unspecified · J | unspecified · W |
| G | `LocalController.control_iterates_eq` | `LocalController.reversible_iff_rows` | `LocalController.two_open_compatible_rules`, `tagged_trace_observable_eq` · S | `BranchPulseContract.comparison_mem` · G | `LocalController.guard_decisions_eq_iff` · G | `LocalController.radius_one` · G | unspecified · G | unspecified · Q | `RingReceiver.mixed_ring_flags` [flag] · D | unspecified · W | unspecified · B | unspecified · J | unspecified · U |
| P | `RootClockCalibration.phase_alias_iff` · T | `RegisterControl.phase_unitary` | unspecified · G | `RootTransferPhase.half_pulse_word` | `TwoSiteHandoff.receiver_half_pulse` | `GluedRegister.crossing_word_glued` | `CarrierEvents.reflection_involutive` | `OddReferenceSource.load_rest_mode` · Q | `BranchPulseContract.program_correct` [comparison] | `CoherentRecordRestoration.prepared_repair` | unspecified · E0 | `RootMaintenance.event_is_root` | `ChargedInsertion.joint_selector`, `HeavyFlipControl.no_root_only_direct_address` · U |
| X | unspecified · E0 | `TwoSiteHandoff.step_trace` [live, record] | unspecified · G | unspecified · E0 | `TwoSiteHandoff.exchange_four_returns` | `LocalController.mixed_open_receiver_destinations` [live, record] | unspecified · U | `OpenHandoff.receiver_trace` [live], `OpenHandoff.acceptance_iff_supply` | `TwoSiteHandoff.exchange_flag`, `RingReceiver.mixed_ring_flags` [flag] | `OpenHandoff.export_trace` [record], `BoundaryErasure.tagged_rule_exports` · S | unspecified · B | unspecified · J | unspecified · W [routed value + live/record destination] |
| L | unspecified · E0 | `TwoSiteHandoff.step_trace` [live, record] | `LocalController.radius_one` | unspecified · E0 | `TwoSiteHandoff.arrivals_observed` [live, record] | `OpenHandoff.address_step`, `EdgeLocality.edge_local_native` | `GluedRegister.crossing_word_glued` | `OpenHandoff.acceptance_iff_supply` [record] | `HandoffAdmittance.node_current`, `TwoSiteHandoff.hop_flag` | `OpenHandoff.export_trace` [record] | unspecified · B | unspecified · E0 | unspecified · L |
| M | unspecified · E0 | `CarrierVacuumSector.range_iff_odd` | unspecified · G | `CarrierEvents.active_card` | unspecified · U | `GluedRegister.crossing_word_glued` | `GenerationWalls.one_class_per_wall` | `ReferenceClassHop.touches_reference_class` | `DiagonalReadout.state_flag`, `EventRequirements.massive_flag` | `CoherentGate.unequal_needs_orthogonal` | unspecified · E0 | `EventRequirements.full_reads_both` · J | `PacketGaugeActions.channel_index_bijective`, `EventRequirements.massive_flag` · O |
| R | unspecified · E0 | `OddReferenceSource.first_wall_ports` · O | unspecified · Q | `OddReferenceSource.loading_pulse_stays_at_rest` | `OpenHandoff.acceptance_iff_supply` [record] | `ReferenceClassHop.stationary_iff` | unspecified · O | `NativeReferenceBackground.stationary_iff` | `OpenHandoff.balanced_basis_repair_flag` [flag] | `RecordSupply.clean_supply` · Q | unspecified · B [reset baseline] | `SharedReference.shared` · J | `ElectricHeavyRecord.colour_reference_toll` / `lepton_reference_toll` · J |
| D | unspecified · E0 | unspecified · E0 | unspecified · D | unspecified · E0 | unspecified · E0 | unspecified · E0 | unspecified · E0 | unspecified · E0 | `DiagonalReadout.flag_bounds`, `TollAmplitude.wireAmplitude_sq` | unspecified · W [flag versus stored bit] | unspecified · B [flag versus booked export] | `NetCost.expected_count_linear` · K | unspecified · W [executed comparison + booked flag] |
| F | unspecified · E0 | `CoherentRecordRestoration.unitary_reset_factorization` [record] | unspecified · G [retained record feedback] | unspecified · G | `RecordSupply.live_at_site`, `OpenHandoff.receiver_trace` [record] | `OpenHandoff.export_trace` [record] | unspecified · U | `RecordSupply.ring_returns`, `CoherentRecordRestoration.twice_undoes` | `OpenHandoff.receiver_flag` [flag] · D | `RecordTransport.tick_fifo`, `stream_conserved` | `BoundaryErasure.open_export_source`, `BoundaryErasure.erasing_pays_one` · B [booked export] | unspecified · J | unspecified · W [retained/exported record port] |
| B | unspecified · E0 | `BoundaryErasure.identity_bijective` | unspecified · B | unspecified · E0 | unspecified · E0 | unspecified · B | unspecified · E0 | unspecified · Q [physical ready state] | `BoundaryErasure.erasing_pays_one`, `ring_erasure_survivor_eq` · H | `BoundaryErasure.kept_bit_injective` / `recycled_bit_injective` · B [return wiring] | `BoundaryErasure.erased_bit_merges` | `BoundaryErasure.policy_cycle_counts_booked_exports` · K | `WireReferenceCost.reference_threshold_with_erasure` · B |
| A | unspecified · T | unspecified · J | unspecified · J | `RootMaintenance.canonical_is_root` | unspecified · J | unspecified · J | unspecified · E0 | `CoherentRefresh.minimum_once`, `WireReferenceCost.shared_maintenance_free` · J | `RefreshSchedule.minimal_is_ledger` · K | unspecified · J | unspecified · B | `PersistenceSelection.within_family_iff_cheapest` · H | `WireReferenceCost.shared_maintenance_free` · J |
| E | unspecified · E0 | unspecified · E0 | unspecified · U | unspecified · U | unspecified · W | unspecified · U | `ChargedInsertion.vector_static_leg` · U | unspecified · J | `ElectricHeavyRecord.two_bit_factor_toll`, `EventRequirements.massive_flag` | `HeavyFlipRecords.orbit_record_tolls` · W [record polarity] | unspecified · B | `WireReferenceCost.booked_population_difference` · H | `ChargedInsertion.joint_selector`, `WireReferenceCost.reference_threshold_with_erasure` · U |

### Classification

Here **free input** means open at this interface in the current library.
It can still be derived by future work. A named output is a conditional
consumer of that input. It need not have a physical value yet.

| ID | Class | Missing input or certified reason | Quantity it affects |
| --- | --- | --- | --- |
| E0 | E8-fixed in the encoded operations | The typed update and its projections have no argument of the indicated kind at that direct port. The endpoint domains below give the scope. This class makes no claim of a physical absence in the full lattice. | None through that direct port of the certified operation. |
| S | Symmetry on tagged traces | `LocalController.tagged_trace_observable_eq` and `BoundaryErasure.tagged_rule_exports` identify the entire tagged retained trace and its export under AND/OR. | Every common observation of that trace. The mixed-input witness lies outside this symmetry. |
| T | Free input · Absolute timing | Assign the physical tick, pulse area, serial placement and allowed overlap for an admitted word. This includes capacity left in a period and any clock-specific price. | Route periods, physical `r`, and which setup/refresh/write fits in the frame. |
| O | Free input · Background occupancy | Specify accessible occupied ports, the actual packet ensemble, its empty-slot treatment and the initial reference and request fibres. | Writer population and sampling threshold, basis-loading capacity and trial history counts. |
| G | Free input · Joint controller | Specify which local conditions enable the shift, pulse, wall loader and receiver. Include retained-record feedback and any throttling outside the finite table. The certified table count is not such a rule. | Executed branch, pulse word, realized crossing and receiver flag. |
| L | Free input · Physical link admission | Specify occupied edges, available link capacity and disturbance, and the through law conditional on earlier crossings. | Route availability and the realized transmission product or restoring weight. |
| Q | Free input · Supply and acceptance | Specify ready-state supply, accepted disturbance and available return capacity at repeat visits. Stationary modes and the population lower bound are conditional on their setup. | Clean visits, restoration and reuse of the writer reference. |
| D | Free input · Physical observation | Specify the detector's read support and its connection to the flags, including whether a controller sees that flag. The conditional flag formula already applies on a supplied state. | Detected or booked flag count and any flag-controlled pulse. |
| K | Free input · Registration tariff | Specify booked comparisons and distinct paid preparation, crossing, export, reset or reuse. A current coefficient, activation probability or minimum at given prices is not a tariff for these stages. | Schedule and label Toll, wire amplitude and signed remaining reference cost. |
| W | Free input · Mixed receiver readout | Attach the writer or insertion to the routed value **and** destination, a retained/exported record, or the executed comparison and its booked flag, as required by that consumer. The certified EP trace supplies none of these attachments. | Routed payload and writer sampling, or receiver Toll and hence insertion amplitude. |
| B | Free input · Boundary disposition | Specify which record becomes a booked export, whether it is retained, returned or erased, and the capacity and return connection of that endpoint. | Erased bits per period, restored reference and the erased-bit difference in the reference threshold. |
| J | Free input · Job ownership and contention | Specify simultaneous jobs, contending uses, and equality of state, time and resource for shared service. | Schedule capacity, reuse and incremental maintenance cost. |
| H | Free input · Prior and selection family | Specify the compared histories and their prior. `BoundaryErasure.ring_erasure_survivor_eq` returns the normalized supplied prior on the retained ring. | Aggregate survival for receiver rules and expected writer Toll. |
| U | Free input · EP joint admission | Specify the embedding of admitted traffic, seed, wall and pulse into the heavy writer or static charged insertion. | Heavy branch, record reference, lightest offset, tier identification and the physical orders in `1/Δ`. |

For E0 the endpoint domains are the finite phase and supplied mask
(`CarrierReferenceCycle.clock`, `ClockedRootTrials.tick`), retained
controls and left-live/right-record arrivals
(`LocalController.radius_one`), encoded banks
(`IndependentRegisters.sectorEquiv`, `RegisterControl.extend_encode`),
the supplied root word and link field
(`BranchPulseContract.program_correct`, `NativePacketUpdate.native_local`),
carrier/class and reference coordinates
(`CarrierVacuumSector.range_iff_odd`, `ReferenceClassHop.stationary_iff`),
supplied detector state and record payload
(`DiagonalReadout.state_flag`, `RecordTransport.tick_fifo`), and
the booked bit or job list (`BoundaryErasure.identity_bijective`,
`RefreshSchedule.minimal_is_ledger`). EP formulae take the explicit
packet/wall, phase and cost arguments in `ChargedInsertion.joint_selector`
and `WireReferenceCost.reference_threshold_with_erasure`. E0 rules out
an extra argument in those operations. An additional direct physical
connection would need its own specification. The W cells track the
specific uninstantiated connection already identified by admission.

**Derived mixed input.** `LocalController.mixed_open_receiver_destinations`
sends the same marked value to record at −1 under AND and live at +1
under OR. `RingReceiver.mixed_ring_flags` yields flags 0 and 1 in its
mixed-basis witness. X → E asks whether EP receives the first kind of
datum. D → E asks whether it receives the paid second kind. F → E asks
where the retained or exported record can be read. A comparison flag
and an erased exported bit belong to different accounts. No full
receiver-rule symmetry follows.

## Where the earlier questions sit

| Earlier level | Cell or pillar | Open question |
| --- | --- | --- |
| Price | D → A, P Toll, B → D | Which work is booked, and which exported bits are erased? K, B. |
| Schedule | A → G, A → X, A Protocol | Which visits are required, concurrent and separately paid? J, K. |
| Clock | C → P, C → E | Which physical tick and area realize the candidate word? T. |
| Selection | A → A, A → E | Which traces and paid costs enter the comparison? H, K. |
| Admission | N → G, R → X, E Governor | Which occupied states, references and EP attachments are accessible? O, Q, U. |
| Update rule | G → P, G → X, F → G | How do the retained records control pulses, routing and readiness? G. |
| AND/OR | G → X, X → L, X → D | The mixed receiver branch, destinations and flags differ. Its downstream use is W. |
| Prior | B → D, A → A | Which initial histories carry prior mass? H. |
| Export contract | F → B, X → E, D → E, F → E | Which routed value, record or paid comparison is read, and what is disposed after the last use? W, B. |
