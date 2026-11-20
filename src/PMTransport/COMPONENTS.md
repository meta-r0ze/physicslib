# PMTransport components

This is an inventory of the lattice-node model. Each node has retained
registers, local controls and a receiver. The encoded line and rings use
a common clock, the same rule at each site and two directed streams.
The packet has 16 slots. The boundary can account for erasure of a booked
export, separately from the reversible internal step. The Boolean line
and ring states and the 16-slot carrier are separate encodings. Their
reversible lifts preserve the core projection. Their physical packet
operation and its clock placement remain open.

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
| Clock | `Values.Delta_eq` | `Components.trial_slot_margin` · T/J | `CarrierReferenceCycle.clock_closes` | `ClockedRootTrials.quiet_trial_tick` | global only · T | `CarrierReferenceCycle.clock_visits` · T |
| Node registers | `TwoSiteHandoff.port_count` | missing · O | `RegisterControl.occupation_conserved` | `IndependentRegisters.occupied_encode` | global only · K | `LocalController.radius_one` · G/J |
| Controller | `LocalController.enumerated_rule_count` | `Components.ring_exchange_full_load` · O | `LocalController.reversible_iff_rows` | `LocalController.radius_one` | No receiver flag booking in the core · K/D | `Components.line_receiver_phaseLoad_le` · G |
| Root and selector pulses | `CarrierEvents.active_card` | N/A · NA4 | `RootTransferPhase.phase_unitary` | `BranchPulseContract.program_correct` | `CarrierEvents.uniform_activation` · K | `Components.trial_phaseLoad_le` · G/T |
| Receiver | `TwoSiteHandoff.port_count` | `Components.ring_exchange_full_load` · Q | `TwoSiteHandoff.exchange_four_returns` | `LocalController.receiver_realisation` | `RingReceiver.mixed_ring_flags` · K | `Components.line_receiver_phaseLoad_le` · G |
| Links | N/A · NA1 | N/A · NA1 | `OpenHandoff.address_step` | `OpenReferenceFlow.bypass_transmits` | `HandoffAdmittance.node_current` · K | `Components.ring_source_neighbour` · G/L |
| Carrier and payload | `CarrierEvents.carrier_card`, `PacketGaugeActions.channel_index_bijective` | missing · O | `CarrierEvents.reflection_involutive` | `GenerationWalls.one_class_per_wall` | global only · K | `NativePacketUpdate.native_local` · G/T |
| Reference and preparation | `SharedReference.reserved_single` | `OddReferenceSource.odd_reference_population` · Q | `SharedReference.shared` | `OpenHandoff.acceptance_iff_supply` | missing · K | `OpenHandoff.receiver_trace` · Q/T |
| Readout and flag account | missing · D | `DiagonalReadout.flag_bounds`, `Components.ring_flag_margin_attained` · D | `DiagonalReadout.state_flag` | `BranchPulseContract.program_correct` | `InBandRootReadout.expected_read_undo_cost` · K/D | `Components.ring_flag_le_one` · D/T |
| Record path | `RecordTransport.history_memory_bound` | missing · Q | `RecordTransport.stream_conserved` | `OpenHandoff.sum_exported` | missing · K | `Components.fifo_tick_ports` · W/T |
| Boundary and sink | `BoundaryErasure.disposition_count` | `Components.erasure_margin_attained` · B | `BoundaryErasure.identity_bijective` | `BoundaryErasure.erased_bit_merges` | `BoundaryErasure.erasing_pays_one` | `Components.cycle_erased_le_period` · B |
| Maintenance and job coordination | N/A · NA2 | N/A · NA2 | `RootMaintenance.event_is_root` | `RefreshSchedule.minimal_is_ledger` | missing · K | `RootMaintenance.event_is_root` · J/T |
| EP writer and insertion endpoint | `PacketGaugeActions.channel_index_bijective` | N/A · NA3 | `GenerationWalls.one_class_per_wall` | missing · W | `Values.outputFlagThreshold_eq`, `Values.balancedResetThreshold_eq` · K | missing · U/T |

### Not applicable

| ID | Pillar cells | Reason and owning interface |
| --- | --- | --- |
| NA1 | Links Capacity and Margin | An edge is the address and transport map. It holds no persistent store. Traffic limits belong to the node ports and schedule (G/L/T). |
| NA2 | Maintenance Capacity and Margin | The job list coordinates other registers. It has no reserve of its own. Contention for the registers and clock stays J/T. |
| NA3 | EP endpoint Margin | This is the declared Transport-to-EP read interface. It has no stored reserve. Accessible writer inputs stay O/W. |
| NA4 | Root and selector pulse Margin | A pulse is an operation on a register. Positive quarter-time is a time bound. Available slack belongs to the clock and register, under T/J. |

These entries remove no clock, traffic, work or occupancy requirement
from the owning component.

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
| G | `LocalController.control_iterates_eq` | `LocalController.reversible_iff_rows`, `Components.joint_line_bijective_iff` | `LocalController.two_open_compatible_rules`, `tagged_trace_observable_eq` · S | `BranchPulseContract.comparison_mem` · G | `LocalController.guard_decisions_eq_iff` · G | `LocalController.radius_one` · G | unspecified · G | unspecified · Q | `RingReceiver.mixed_ring_flags` [flag] · D | unspecified · W | unspecified · B | unspecified · J | unspecified · U |
| P | `RootClockCalibration.phase_alias_iff` · T | `RegisterControl.phase_unitary` | unspecified · G | `RootTransferPhase.half_pulse_word` | `TwoSiteHandoff.receiver_half_pulse` | `GluedRegister.crossing_word_glued` | `CarrierEvents.reflection_involutive` | `OddReferenceSource.load_rest_mode` · Q | `BranchPulseContract.program_correct` [comparison] | `CoherentRecordRestoration.prepared_repair` | unspecified · E0 | `RootMaintenance.event_is_root` | `ChargedInsertion.joint_selector`, `HeavyFlipControl.no_root_only_direct_address` · U |
| X | unspecified · E0 | `TwoSiteHandoff.step_trace` [live, record] | unspecified · G | unspecified · E0 | `TwoSiteHandoff.exchange_four_returns` | `LocalController.mixed_open_receiver_destinations` [live, record] | unspecified · U | `OpenHandoff.receiver_trace` [live], `OpenHandoff.acceptance_iff_supply` | `TwoSiteHandoff.exchange_flag`, `RingReceiver.mixed_ring_flags`, `Components.ring_observations_local` [flag] · D | `OpenHandoff.export_trace` [record], `BoundaryErasure.tagged_rule_exports` · S | unspecified · B | unspecified · J | unspecified · W [routed value + live/record destination] |
| L | unspecified · E0 | `TwoSiteHandoff.step_trace` [live, record] | `LocalController.radius_one` | unspecified · E0 | `TwoSiteHandoff.arrivals_observed` [live, record] | `OpenHandoff.address_step`, `EdgeLocality.edge_local_native` | `GluedRegister.crossing_word_glued` | `OpenHandoff.acceptance_iff_supply` [record] | `HandoffAdmittance.node_current`, `TwoSiteHandoff.hop_flag` | `OpenHandoff.export_trace` [record] | unspecified · B | unspecified · E0 | unspecified · L |
| M | unspecified · E0 | `CarrierVacuumSector.range_iff_odd` | unspecified · G | `CarrierEvents.active_card` | unspecified · U | `GluedRegister.crossing_word_glued` | `GenerationWalls.one_class_per_wall` | `ReferenceClassHop.touches_reference_class` | `DiagonalReadout.state_flag`, `EventRequirements.massive_flag` | `CoherentGate.unequal_needs_orthogonal` | unspecified · E0 | `EventRequirements.full_reads_both` · J | `PacketGaugeActions.channel_index_bijective`, `EventRequirements.massive_flag` · O |
| R | unspecified · E0 | `OddReferenceSource.first_wall_ports` · O | unspecified · Q | `OddReferenceSource.loading_pulse_stays_at_rest` | `OpenHandoff.acceptance_iff_supply` [record] | `ReferenceClassHop.stationary_iff` | unspecified · O | `NativeReferenceBackground.stationary_iff` | `OpenHandoff.balanced_basis_repair_flag` [flag] | `RecordSupply.clean_supply` · Q | unspecified · B [reset baseline] | `SharedReference.shared` · J | `ElectricHeavyRecord.colour_reference_toll` / `lepton_reference_toll` · J |
| D | unspecified · E0 | unspecified · E0 | unspecified · D | unspecified · E0 | unspecified · E0 | unspecified · E0 | unspecified · E0 | unspecified · E0 | `DiagonalReadout.flag_bounds`, `TollAmplitude.wireAmplitude_sq` | unspecified · W [flag versus stored bit] | unspecified · B [flag versus booked export] | `NetCost.expected_count_linear`, `Components.booked_toll_sum` · K | unspecified · W [executed comparison + booked flag] |
| F | unspecified · E0 | `CoherentRecordRestoration.unitary_reset_factorization` [record] | unspecified · G [retained record feedback] | unspecified · G | `RecordSupply.live_at_site`, `OpenHandoff.receiver_trace` [record] | `OpenHandoff.export_trace` [record] | unspecified · U | `RecordSupply.ring_returns`, `CoherentRecordRestoration.twice_undoes` | `OpenHandoff.receiver_flag` [flag] · D | `RecordTransport.tick_fifo`, `stream_conserved`, `Components.joint_fifo_restriction` · T | `BoundaryErasure.open_export_source`, `BoundaryErasure.erasing_pays_one` · B [booked export] | unspecified · J | unspecified · W [retained/exported record port] |
| B | unspecified · E0 | `BoundaryErasure.identity_bijective`, `Components.joint_boundary_identity` | unspecified · B | unspecified · E0 | unspecified · E0 | unspecified · B | unspecified · E0 | unspecified · Q [physical ready state] | `BoundaryErasure.erasing_pays_one`, `ring_erasure_survivor_eq` · H | `BoundaryErasure.kept_bit_injective` / `recycled_bit_injective` · B [return wiring] | `BoundaryErasure.erased_bit_merges` | `BoundaryErasure.policy_cycle_counts_booked_exports` · K | `WireReferenceCost.reference_threshold_with_erasure` · B |
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
| Price | D → A, P Toll, B → D | The supplied total reconciles. Physical booking and export stay K/D/B. |
| Schedule | A → G, A → X, A Protocol | Encoded rates bound one instance. Joint slot ownership and work stay J/T/K. |
| Clock | C → P, C → E | The isolated trial leaves 41 slots. Calibration and placement stay T. |
| Selection | A → A, A → E | Which traces and paid costs enter the comparison? H, K. |
| Admission | N → G, R → X, E Governor | Which occupied states, references and EP attachments are accessible? O, Q, U. |
| Update rule | G → P, G → X, F → G | The core and FIFO lift separately. Physical packet firing and feedback stay G/T/U. |
| AND/OR | G → X, X → L, X → D | The mixed receiver branch, destinations and flags differ. Its downstream use is W. |
| Prior | B → D, A → A | Which initial histories carry prior mass? H. |
| Export contract | F → B, X → E, D → E, F → E | All receiver candidates are local. W/D say which one is read. B says what is disposed after use. |

## Per-instance rates

Use the substrate phase as the time unit here. These are bounds of the
specified encodings. T still decides elapsed pulse time, sharing and
parallel instances. G and O govern which opportunities are used.

| Part | Per tick and per period | Scope or open rate |
| --- | --- | --- |
| Clock | One phase advance. Visits 43 phases before closing. | `CarrierReferenceCycle.clock_visits`, `clock_closes` and `Values.Delta_eq`. Physical frequency is T. |
| Node registers | Two output stream slots per site step. | `TwoSiteHandoff.step_trace` and `LocalController.radius_one`. Separate bank writes and simultaneous jobs are G/J. |
| Controller | One receiver decision per site and phase, at most 43 exchanges per period. | `Components.line_receiver_phaseLoad_le`. `ring_receiver_phaseLoad` is exact for fixed requests. Retained trial probes have a separate budget. |
| Root and selector pulses | One possible fire at each trial slot, at most two in its period. | `Components.trial_phaseLoad`, `trial_phaseLoad_le`. Other pulse words need T and G. |
| Receiver | Two arrivals and at most one exchange per site and tick. One displaced record per visit on the supplied open exchange line. | `LocalController.receiver_realisation`, `OpenHandoff.receiver_trace`, `Components.line_receiver_phaseLoad_le`. The encoded open line has 43 visit slots per period. |
| Links | One adjacent hop per stream per step. Each ring output reads one of its two adjacent source sites. | `Components.ring_source_neighbour`, `RingReceiver.port_step_source`, `OpenHandoff.address_step`. The chain of physical 16-slot hops has no joint clock assignment (T/G). |
| Carrier and payload | One source edge per output of the supplied native hop. | `NativePacketUpdate.native_local`. No number of these hops per substrate tick follows (T/L). |
| Reference and preparation | One ready record supplied per exact open visit. | `OpenHandoff.receiver_trace`, `basis_population_required`. Preparation and renewal cadence is Q/T. |
| Readout | The specified ring receiver returns one flag of size at most one per site step. | `Components.ring_flag_le_one`. Other detector counts require D and T. |
| Record path | One FIFO output and one incoming packet accepted per FIFO step, with the record bank shifted. | `RecordTransport.tick_fifo`, `Components.fifo_tick_ports`. FIFO steps per physical tick are T. |
| Boundary | At most one booked exported bit erased per port per tick, and at most 43 per port per period. | `Components.erased_bits_le_one`, `cycle_erased_le_period`. Actual exports and disposition are B. |
| Maintenance | A specified job uses one root event. | `RootMaintenance.event_is_root`. Jobs fitting simultaneously or per period are J/T. |
| EP endpoint | Logical comparisons per candidate write or insertion. | [Clock requirements](CLOCK.md#slot-requirements-for-a-wire-cycle). Clock placements and admitted consumer visits are T/U. |

## Margin in matching units

| Encoded reserve | Capacity and maximum load | Worst-case margin |
| --- | --- | --- |
| Clock slots left by the isolated trials | 43 phases, at most two fires, both attainable | 41 unused trial slots. `Components.trial_slot_margin` and `trial_slot_margin_attained`. Shared capacity remains T/J. |
| Controller and receiver exchange opportunities | 43 opportunities and 43 possible exchanges for each rule | Zero unused opportunities at maximum load. `Components.ring_exchange_full_load`. This counts operations, even on equal values. |
| Specified comparison flag | One unit and an attained unit flag for the OR basis witness | Zero headroom in flag units in this case. `Components.ring_flag_margin_attained`. This is independent of booking. |
| Boundary per binary export port | 43 opportunities and 43 possible erased bits | Zero unused slots at maximum load. `Components.erasure_margin_attained`. The retained ring uses zero and leaves the entire accounting capacity unused. |

Each pair uses the same unit. A carrier count does not bound the number
of occupied jobs or the number of pulses per tick. The two stream outputs
and FIFO arity describe slots rather than occupancy. A ready reference
requires supply. The remaining applicable margin entries require the inputs shown above. A physical reserve cannot be assigned from those slot counts.

## Joint update and its limit

`Components.PacketBank` encodes one incoming 16-slot packet at cell
zero and the retained record packets at the other cells. The product
with the retained controller state keeps the distinct encodings visible.
`jointTick` gives a reversible extension when the core is reversible
and each supplied packet-bank action is a permutation.
`joint_lift_iff` classifies all reversible lifts of that fixed core.
Each has exactly one fibre permutation at each core input.
`joint_core_iterate` commutes with the core projection at every tick,
so the line and ring traces and the trial probe projection survive.
`joint_fifo_restriction` gives the certified FIFO when the fibre
operation is that FIFO. `fifoEquiv_eq_tick` identifies it on amplitudes.
It is a FIFO step, with no inference that a physical carrier crossing
runs at that phase.

`joint_line_bijective_iff` keeps exactly the retained line row
condition. `joint_ring_bijective` keeps either ring reversible.
`joint_boundary_identity` applies the certified disposal operation
after projecting to a separate booked export and leaves the joint
protected permutation bijective. The exported erasure still merges
bits under `BoundaryErasure.erased_bit_merges`.

There is a two-case witness at a phase whose FIFO placement is open.
Holding the bank and executing its existing FIFO give identical
core projections, but can give different outgoing packet amplitudes
even with one record cell (`joint_two_fifo_placements_differ`).
This is the smallest witness to nonuniqueness of the encoded lift.
It is neither a catalog of physical schedules nor a choice of one.
Forcing both full factor projections would *impose* an independent
product (`joint_fixed_projections`). The certified FIFO law gives
the result of a FIFO firing. It does not impose such a projection at
every controller tick. The native single-edge hop and the EP
packet/class operators have their own state and supplied controls.
An intertwining theorem to a chosen 16-slot wire update is still needed.

Across the family, the core-projected clock, requests, receiver
branch, Boolean destinations, flags and tagged exports are the same
at a common core rule and start. So are the parameter-free values
and conditional formulae in [DOWNSTREAM](DOWNSTREAM.md). The joint
packet output, effective writer population and paid work can depend
on the supplied packet-bank action and reader attachment.

| Gap | What the lift narrows | What remains |
| --- | --- | --- |
| G | Reversibility and projected guards for both existing core encodings. | Which local conditions and phases enable the actual packet operation. |
| U | FIFO on all 16 packet coordinates when that operation runs. | Identify the wire and EP operator on that joint trace, including carrier crossing and charged insertion. |
| O | Core request fibres and encoded traffic still project exactly. | Accessible joint starts and occupancy, including boundary supply. |
| W | Projected core observables are independent of the bank action. | Which projected or packet-bank output is supplied to the EP reader. |

## Fan-out at a receiver

`Components.ring_observations_local` puts the two output values and
the comparison flag in the same read neighbourhood. Each depends
on the local requests and the two adjacent arrivals. The guard
determines outgoing stream identity at that event. Following a stream
to another node requires its next shift. Local determination provides
no clock slot or input port to an EP consumer. It does exclude
reconstructing arbitrary later arrivals from the same initial local
stencil (`OpenHandoff.neighbours_do_not_determine_second_visit`).

| Possible attachment at the visit | Locally determined datum | Downstream consequence if attached |
| --- | --- | --- |
| X → E | Routed value plus live/record destination. The destination on the next link follows the outgoing stream. | Producer of the writer's payload and therefore its input distribution and slot counts. The mixed witness can route to different ports. |
| F → E | Occupied retained record at a supplied local or arriving slot. A later export is a different visit. | Supplies the writer polarity, readiness or insertion guard when the physical encoding makes the record such an input. |
| D → E | Executed comparison and its mismatch result on that input. | May furnish a registration and the Toll in `exp(−T/2)`. A zero flag can accompany an executed exchange. |

All three are cases of W. The clock permits reasoning about when the
core values are available. The EP read event, its position relative
to that tick and its attachment still require W/T/U. No case follows
as the sole physical attachment.

## Readout consumption

Apply the registration test to a specified trace. A read or a persisted
record makes the result a registration in the stated account. An
analytical flag or response can be evaluated from the same trace
without a machine read. The cost of running a gate is a separate
question, even when its flag is zero.

| Flag or readout family | Consumer in the existing encoding | Registration status |
| --- | --- | --- |
| Ring and line receiver exchange flags | `RingReceiver.receiverFlag` and `LocalController.exchangeFlag` are observables. The core step reads the requests and arrivals and routes the values. The ring orbit average and uniform line flag ledgers are external evaluations. | Unregistered by the specified core tick. A local detector or persisted comparison output would need D/W. |
| Two-site hop and exchange, open receiver | `TwoSiteHandoff.hop_flag`, `exchange_flag` and `OpenHandoff.receiver_flag` compare supplied coherent states. The record stream retains the displaced value. | No flag booking follows from carrying that value. A comparison consumer at that visit needs D. |
| Root phase and carrier response, calibration and order comparisons | `RootPulseEvents.phase_flag`, `CarrierResponse.reflection_flag`, `RootClockCalibration.principal_flag_inj` and `RootOrderComparison.native_flag` evaluate supplied comparisons. The trial retains its requests and probe endpoint. | The trial endpoint is retained. A measured comparison of the endpoint, or a different phase detector, still needs D and the scheduled read. |
| Reference sampling and preparation/reset comparisons | `ReferenceSampling.ref_flag`, `SummedReference.sum_flag`, `RootReferencePreparation.setup_comparison_flag` and `OpenHandoff.balanced_basis_repair_flag` evaluate supplied reference states and detector comparisons. | Preparation and coherent return can write a state. A booked setup/reset comparison needs the specified support and consumer. Binary erasure is separate. |
| Matched lattice, parity and in-band readers | `ScheduledReadout.readGate`, `ParityReadoutCircuit.prepared_read`, `InBandRootReadout.clean_record_reads` write a result to the designated register when the prepared read executes. | Recorded within those supplied read operations. Admission of the physical read, detector/accumulator support and its tariff are still D/G/K. |
| Interference and diagonal phase flags, including EP massive flags | `InterferenceReadout.flag_formula`, `DiagonalReadout.state_flag` and `EventRequirements.massive_flag` are probabilities on supplied detector inputs. | The formula alone makes no registration. Need the detector support and visit. |
| Heavy writer and charged insertion | `HeavyFlipRecords.orbit_record_tolls` and `ElectricHeavyRecord.two_bit_factor_toll` count specified logical comparisons. The guarded companion uses a supplied record. `ChargedInsertion.joint_selector` uses the retained selected branch. | Recorded or read when the stipulated circuit with those banks is executed. Its detector/projection and attachment to the admitted trace are D/W/U. A flag or projector expectation alone is no extra registration. |

The missing detector support specifies the occupied input, clock
phase, result slot or consumer, and the last use of each result.
It distinguishes the internal readout from an external observation
and distinguishes a retained bit from a booked exported bit.

## Toll by operation

`Components.booked_toll_sum` partitions supplied booked unit
registrations by component owner. It equals
`NetCost.expectedCost` on the same events, plus the separately booked
boundary erasures. Each registration must be a single event in that
list. Multiple readers do not prove multiple executed writes. The
identity uses the uniform law on the supplied sample space of
`NetCost`. A nonuniform law still needs its supplied masses and the
weighted accounting rule (`EventAccounting.weighted_linear`).

| Component | Certifiable account | Stage still missing |
| --- | --- | --- |
| Clock | Clock phase and duration bounds. | Price of physically advancing and sharing the clock. |
| Registers | Occupation is conserved under the encoded update. | Cost of a physical read, write or preparation outside the specified counters. |
| Controller | Null receiver flag registration in the retained tick without an attached detector. | Cost of switching or retaining the physical guard. |
| Pulses | `CarrierEvents.uniform_activation` counts a supplied uniform primitive activation. | Primitive tariffs and which complete word is run and paid. |
| Receiver | The branch and flag are computed on the stated arrivals. | Physical flag booking and any separate receiver work. |
| Links | Conditional current and admittance. | Price of the executed crossings and traffic. |
| Carrier | Slot and wall dimensions. | Paid work for the actual carried label and wall. |
| Reference | Exact supplied restoration and conditional preparation/reset flags. | Seed and maintenance price and its reuse at a common visit. |
| Readout | `InBandRootReadout.expected_read_undo_cost` prices the actual two root events on the clean norm-two sample at the supplied unit price. | Selection of that detector and the tariff for other detectors and gates. |
| Records | Logical record preservation and FIFO. | Physical write, hold, export and reuse, plus any reset other than a booked erase. |
| Boundary | One Toll per booked erased bit. Zero on the certified retained ring. | Which physical bits reach the port and their disposition. |
| Maintenance | Minimum supplied job ledger under `RefreshSchedule.minimal_is_ledger`. | Job ownership, shared upkeep and remaining prices. |
| EP | Conditional output flag and balanced reset thresholds. | Booked visits, writer population and the difference in all other work, including any actual erasure reset. |

`NetIndex.index_as_net_transitions` is the substrate's six-term
baseline. The partition identity checks equality to the supplied
`NetCost` event total. There is no identification of these machine
visits and erasures with the baseline provisioning and removed-event
sets. An equality to that global index remains an event-identification
input under K, rather than another rate or scalar tariff.

## Admission recheck

**S, tagged core only.** The joint lift projects to the original
core at every tick. The common tagged open trace still gives the
same observations under AND and OR
(`LocalController.tagged_trace_observable_eq`). At a common initial
packet bank, the same fibre action on both rules preserves equality
of the full tagged lift (`Components.joint_tagged_ticks_equal`). This
does not permit two different packet actions or reader attachments
to be treated as one.

**Derived distinction.** At the mixed witness the Boolean
destinations still differ, and the computed basis flags are still
0 and 1 (`LocalController.mixed_open_receiver_destinations`,
`RingReceiver.mixed_ring_flags`). A pure core transition books
neither flag. If a detector books exactly that comparison, its
conditional unit gap survives. If a writer reads the routed value,
the relevant difference is its destination, even without a flag
registration. Neither attachment follows from the lift.

**B and H remain.** `BoundaryErasure.tagged_rule_exports` ties the
tagged export train with common disposal. `ring_cycle_erasure`
gives zero for the retained ring. `ring_erasure_survivor_eq`
therefore leaves the normalized supplied prior. A mixed boundary
export still requires a source port and disposition. Its prior
requires the accessible initial family and its masses. On the
electric writers, a physical erasure-reset threshold still needs
the difference of their booked bit counts.

**Outcome.** No general AND/OR quotient and no selection follow.
The remaining inputs are joint firing and placement (G/T),
accessible starts and supply (O/Q), packet and writer realization
(U), reader attachment and detector support (W/D), the tariff for
remaining work (K), the export contract (B), and the prior over
histories (H). J and L apply where contention, reuse or successive
links affect that trace.

## Remaining free inputs by reach

The ranking counts distinct outputs in this ledger that directly use
each input in at least one certified conditional route or account.
Each output occupies one place in the count. The counts describe
dependency reach, independently of whether the conditional route is
ultimately realized.

| Input | Output count | Affected outputs |
| --- | --- | --- |
| G · Local firing and packet action | 7 | Receiver branch, realized route, writer population, heavy crossing, lightest insertion, physical schedule, per-label Toll. |
| T · Clock placement and calibration | 6 | Physical schedule, elapsed route periods, physical `r`, heavy crossing, lightest insertion, read availability. |
| O · Accessible occupied background | 5 | Trial prior counts, writer population, sampled reference threshold, readiness, reachable wire modes. |
| U · Carrier and EP realization | 5 | Writer population, heavy crossing, lightest insertion, tier identification, scaling in `1/Δ`. |
| W · Reader attachment | 5 | Writer population, record polarity, heavy crossing, lightest insertion, insertion amplitude. |
| K · Paid work and event identification | 5 | Per-label Toll, wire amplitude, reference selection, schedule selection, substrate-index reconciliation. |
| B · Export and disposition | 4 | Erased bits per period, renewed readiness, merged-history weights, erasure-reset threshold. |
| D · Detector support | 4 | Registration count, receiver Toll, insertion amplitude, calibration statistic. |
| J · Shared jobs and contention | 3 | Physical schedule, incremental maintenance Toll, reference selection. |
| Q · Reference supply and acceptance | 3 | Clean visits, sustained renewal, heavy bank readiness. |
| H · History family and prior | 2 | Aggregate receiver survival, expected writer Toll. |
| L · Admitted link and successor law | 2 | Realized route, effective through weight. |

Layering is a separate build decision in [PREMISES](PREMISES.md#layering).
It supplies no physical input to this ranking.

## Marked node symmetries

`Components.NodeSymmetry` tests the embedded sector-preserving
Weyl action. The marked geometry keeps the two D₄ sectors distinct.
The active factor uses signed axis permutations with even sign
parity. The other factor acts independently. The phase is a
separate scalar slot. A spatial sign normal in the slice model is
an extra marking beyond fixing this scalar phase.

| Certified edge family | Active stabilizer | Generators in the active sector | Order with the other marked sector |
| --- | --- | --- | --- |
| All 24 roots of the active sector with no distinguished direction | 192 | Four simple roots. `unsigned_generators`, `diagonal_generators`, `sector_factor`. | 36,864 |
| Open root line, retaining positive direction `e₀ + e₁` | 8 | Simple roots 0, 2, 3 (`line_generators`). | 1,536 |
| Directional axis hop `2e₀` with no slice normal | 24 | Simple roots 1, 2, 3 (`axis_generators`). | 4,608 |
| Axis hop fixing the slice plane, with no marked normal direction | 8 | Swap transverse axes 1 and 2 and flip the pair 2 and 3 (`slice_plane_generators`). | 1,536 |
| Axis hop within the slice with positive clock normal `e₃` | 4 | Swap transverse axes 1 and 2 and change both their signs (`slice_generators`). | 768 |

`stabilizer_orders` and `paired_orders` check the counts.
`simpleFrame_carrier` identifies the carrier action with
`CarrierWeyl.simple`. `simpleFrame_substrate` identifies it with
the embedded E8 reflections and fixes the other sector. The bare
abstract ring supplies oriented shifts and a scalar clock, without
a geometric edge in the E8 lattice. A chosen ring geometry can
use the corresponding marked link result.

The fixed trial reflection uses `e₀ − e₁` in the first sector.
The root-line group preserves it up to sign
(`line_preserves_probe`). The slice group can move it
(`slice_can_move_probe`). Keeping both the positive axis and that
reflection axis fixes `e₁` (`axis_fixed_probe_iff`).
`fixed_probe_orders` gives active order 4 without the slice,
and 1 with a marked normal. `slice_plane_probe_order` gives 2 for
the slice with an unmarked normal. The generators are checked in
`fixed_probe_generators` and `slice_plane_probe_generators`. These extra restrictions apply when the link and
probe use the same marked sector.

`bare_line_mixing_root` gives a norm-two E8 reflection fixing the
positive bare line while mixing the two sectors. Thus forgetting
the markings can enlarge the Weyl stabilizer. No common unmarked edge family, probe and
Weyl action on the controller and 16-slot reader is supplied. The
orders above concern the certified marked families. They give no
order for an arbitrary supplied configuration of links. The
packet weak, colour and hypercharge actions are certified
separately by `PacketGaugeActions`. Their matrices give a uniform
packet action at each bank cell. The library supplies no identification
of that action with the spatial stabilizer or a finite combined order.

## Equivariant lifts

`Components.joint_commutes_iff` is an exact test for a factorwise
action. The core must commute with its relabelling. The packet
permutation at the relabelled input must be conjugate to the
original one by the bank action. This narrows the reversible
family without choosing a packet action.

For the certified weak, colour and hypercharge matrices the same
operator is applied in every cell. Both holding and advancing the
FIFO commute with that action (`hold_fifo_equivariant`). The FIFO
changes the cell and leaves the channel index intact. This also
works for common carrier relabellings on every cell. For
symmetries acting trivially on the marked Boolean core, both AND
and OR commute, so all four combinations of the two guards and
two bank actions survive this test. Two bank choices at fixed
guard already suffice to distinguish the packet projections.
The mixed witness still distinguishes the guards at fixed bank
choice.

For spatial relabellings that preserve the line addresses and
stream orientation, no site or stream swap is induced on that
line. In using a fixed native probe, only symmetries preserving
its reflection axis can commute with the fixed-root pulse in
general. `line_probe_equivariant` checks the line case and
`slice_probe_not_equivariant` exhibits the fixed-root obstruction.
The axis counterexample affects the shared probe on
both guards. It is no evidence against one receiver rule. There
is no certified factorwise action of the full E8 Weyl group on
the Boolean requests, probe and 16-slot packet together.
A stronger equivariance test needs that existing G/U interface
to identify the action. It cannot turn either surviving bank
choice into a unique update on the current interface.

## Conservation filter

| Quantity | Certified conservation and scope |
| --- | --- |
| Register occupation | `RegisterControl.occupation_conserved` on the encoded banks. `NativePacketRouting.registers_conserved` on its supplied routing. |
| Stream totals | `Components.ring_stream_total` preserves the combined live and record total for any value measure. Exchange can transfer between the streams. `OpenHandoff.sum_exported` balances displaced input and the ordered export window, with incoming boundary supply stated. `RecordTransport.stream_conserved` gives the FIFO list law. |
| Packet population and labels | `Components.fifo_channel_total` preserves each channel total across live and retained memory for any amplitude measure. Holding does so immediately. `RecordTransport.tick_norm` gives total norm preservation. For specified hops use `NativePacketUpdate.native_conserving` and `NativePacketRouting.packet_population`. A gauge action may mix coordinates. Gauge charges commuting with a specified action (`PacketGaugeActions.weak_charge`, `colour_charge`) are distinct from individual cell labels. The bank permutation preserves all channel-diagonal population sums. |
| Identity registers | `Components.joint_line_bijective_iff`, `joint_ring_bijective` and `joint_boundary_identity`. Erasure merges a separate exported bit under `BoundaryErasure.erased_bit_merges`. |
| Weyl norm, glue and carrier sector | `SubstrateWeylRoots.preserves_norm`, `preserves_glue`, `CarrierWeyl.simple_is_root`, `CarrierParity.range_iff_odd`, and `ClockControlledRoot.norm_preserved` and `glue_preserved`. The fixed projection continues to use the existing root dynamics. Hold and FIFO leave channel indices unchanged and preserve cell-summed populations in each block. |

The same four hold/FIFO and AND/OR combinations pass the applicable
checks. Per-cell labels, separate live and record totals in an exchange,
and erasure of the identity registers are outside those conservation
claims. Reversible equivariance alone would admit nonconserving
permutations of the amplitude state. For example
`equivariant_lift_can_change_population` supplies a commuting scaling
that changes the norm and is excluded. A physical fibre map must
preserve the quantities appropriate to its carrier embedding.

## Least Toll on certified traces

The [selection theorem](Interface.lean) minimizes the cost within
a supplied admitted family. Compare equal observation windows and
use the same rate units.

| Trace or booking | Certified differential | Consequence |
| --- | --- | --- |
| Tagged open trace with common reader and disposal | Same booked core comparisons and tagged exports. `tagged_trace_observable_eq` and `tagged_rule_exports`. In the all-erase account, each pays one per tick (`open_cycle_erase_all`). | **S** on the tagged read and erasure account. Equal remaining work is needed for equality of the complete Toll. |
| Retained ring without a comparison reader | No comparison registration and no exported erasure. `ring_cycle_erasure`. | The certified subtotal is zero for either guard and either bank placement. Distinguishable outputs still exist. A zero subtotal is a cost tie, not a machine symmetry. |
| Site zero on the occupied mixed ring with the same booked comparisons | `Values.mixedReceiverRate_and` gives zero for AND. `mixedReceiverRate_or` gives the booked fraction of the period for OR. Booking all 43 gives a unit difference per tick. | AND is cheaper in this comparison when its extra remaining rate is smaller than that fraction (`mixed_and_cheaper_iff`). With equal other work and a positive booked fraction it has greater survival. |
| Mixed export or paid FIFO and hold visits | The boundary charges its booked erased bits. The joint lift does not book a comparison, pick the exported port, or price a FIFO write. | The difference needs the existing W/D/B/K inputs. Arbitrary trace averaging also needs O/H. |

Least Toll does not select a physical member from these data.
The identity of the physical comparison and its remaining costs
come before the comparison. A common partial cost does not imply
that the packet, destination or flag factors through a quotient.

## What propagates downstream

G remains open. The top-down checks narrow the admissible fibre
actions by equivariance and conservation, and leave at least the
hold/FIFO witness pair in the certified interface. The previous
[reach ranking](#remaining-free-inputs-by-reach) therefore still
applies. Distinct outputs remain possible even at tied booked cost.

| Input | Narrowed interface | Still needed |
| --- | --- | --- |
| W, attachment | A common read on a common tagged trace is invariant. Mixed receiver outputs and computed flags are local. | Name the live, record or comparison result read by the writer, and its tick. |
| B, export | Identity stays bijective when a separate output is disposed of. Tagged exports agree under common disposal. The encoded ring exports zero. | Identify the physical booked output and disposition, including reset and return wiring. |
| U, carrier to EP | The channel action and conserved totals are explicit on a 16-slot bank. | Intertwine the actual carrier operation and EP label/reader on the same admitted trace. |
| D, detector | A common mask gives the exact conditional mixed flag rate. | Identify the occupied detector support, reader and booking. |

No input in this table is closed on untagged physical traffic.

## Clock placement

Spatial stabilizers fix the scalar phase. This alone places no
operation. The prescribed trial has its own phases 0 and 1. In
the wider closed root-excursion family the one-phase mask at
phase 2 fires at phases 1 and 2
(`Components.shifted_excursion_boundaries`). The period and the
non-idle minimum are the same as for the prescribed excursion
(`ClockControlledRoot.cycle_closes`,
`Components.shifted_excursion_same_cost`,
`CarrierReferenceCycle.minimum_nonidle_carrier_cost`). Fixing
physical pulse or exchange slots still needs the joint placement
and timing T/G. The shift example concerns the excursion family.
It does not move a prescribed trial slot.
