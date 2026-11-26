import PMKAutomaton.Values
import PMKAutomaton.BoundaryErasure
import PMKAutomaton.Machine.CarrierReferenceCycle
import PMKAutomaton.Machine.RecordTransport
import PMKAutomaton.Machine.RootMaintenance
import PMKAutomaton.Machine.SubstrateWeylRoots
import PMKAutomaton.Machine.SliceHop
import PMConstants.PacketGaugeActions
import PMConstants.SharedReference

/-!
# Component contracts

The six fields follow the pillar inventory in the module notes below. Each
constructor uses existing certificates for the stated scope. A named
proposition parameter denotes an unresolved contract. Its statement
and witness must come from the user of the constructor. Global pillar
totals supply no per-component witness.

The contracts are separate. There is no default guard, initial state,
wiring, or disposal policy. The packet and the Boolean controller
remain distinct state spaces.

## Interface, clock and admission notes

### PMKAutomaton components

This is an inventory of the lattice-node model. Each node has retained
registers, local controls and a receiver. The encoded line and rings use
a common clock, the same rule at each site and two directed streams.
The packet has 16 slots. The boundary can account for erasure of a booked
export, separately from the reversible internal step. The Boolean line
and ring states and the 16-slot carrier are separate encodings. Their
reversible lifts preserve the core projection. Their physical packet
operation and its clock placement remain open.

The [open list](TODO.md) owns the physical questions. This page
locates them at component interfaces. [Machine](OVERVIEW.md#native-machine)
indexes the implementation and its continuum applications.
[Interface](Interface.lean) and [Values](Values.lean) remain the certified
KAutomaton entry points. [Components](Components.lean) packages the
pillar certificates with explicit hypotheses for unresolved inputs. No experimental data enters this inventory.

### Components

Unqualified module names refer to the files in Machine, PMKAutomaton,
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
| D | Readout and flag account | `CarrierReadoutQuotient`, `CarrierResponse`, `CarrierProbe`, `MatchedLatticeProbe`, `ReadoutGateBoundary`, `ParityReadoutCircuit`, `InBandRootReadout`, `ScheduledReadout`, `InterferenceReadout`, `DiagonalReadout`, `NetCost`, `TollAmplitude` | `DiagonalReadout.state_flag` computes the weighted phase flag. `NetCost.expected_count_linear` adds expected registrations under its measure. `EffectiveAction.attenuationWeight` at unit scale evaluates survival amplitude for a supplied Toll. |
| F | Record path | `CoherentGate`, `CoherentRecordRestoration`, `RecordTransport`, `WalkRecordTransport`, `WalkReferenceCoupling`, `WalkReferenceProtocol`, `WalkReferenceCycle`, `RecordSupply`, `RecordFeedbackBoundary`, `PrimitiveRecordBoundary` | `CoherentGate.unequal_needs_orthogonal` distinguishes unequal writes. `RecordTransport.tick_fifo` moves records and `OpenHandoff.sum_exported` preserves exported population. |
| B | Boundary and sink | `BoundaryErasure`, `OpenHandoff`, `NativeLocalityBoundary`, `HomogeneousRouting` | `BoundaryErasure.identity_bijective` concerns protected registers. `erasing_pays_one` concerns a booked exported bit. `ring_cycle_erasure` is zero in the retained ring. |
| A | Maintenance and job coordination | `RefreshSchedule`, `CoherentRefresh`, `ReferenceMaintenance`, `RootMaintenance`, `FactorRepair`, `PersistenceSelection` | `RootMaintenance.event_is_root` realizes the given job. `CoherentRefresh.minimum_once` gives the once-per-item optimum at positive prices. `PersistenceSelection.within_family_iff_cheapest` compares supplied candidates. |
| E | EP writer and insertion endpoint | `HeavyFlipControl`, `HeavyFlipRecords`, `ElectricHeavyRecord`, `ElectricCompanionBank`, `ElectricCompanionSetupToll`, `ChargedInsertion`, `EventRequirements`, `WireSchedule`, `WireReferenceCost` | `ElectricHeavyRecord.root_writer` and `ChargedInsertion.joint_selector` give conditional operations. This is a downstream endpoint. The KAutomaton scaffold carries only its upstream contracts. |
The control profiles, root-word encoders and continuum limits are link
implementations and analyses. `ConstantControls`, `ProfileControls`,
`FiniteRootWordControls`, `ConfigurationControls`, `D4EdgeSeparation`,
`NativeConsistency`, `CompactLimits` and `MatterContinuum` cover supplied
controls and their limits. They add no runtime ports to the discrete
machine. The preparation variants, companion bank, parity probe, FIFO
and feedback are included in their owning components above.

### Engineering checklist

| Check | Status | Scope |
| --- | --- | --- |
| Arbiter for contending visits | Missing · J | `RefreshSchedule.minimal_is_ledger` and `CoherentRefresh.minimum_once` certify a schedule for a supplied required set and prices. No joint arbitration on a common clock is supplied. |
| Ground or shared reference | Defined in Lean | `SharedReference.shared` identifies the reserved cell for the weak and hypercharge layout. `ColourReference.colour_reference_in_payload` locates its separate reference. Writer sharing at the same state and time is open · J. |
| Termination and sink | Defined in Lean for candidates · B | `OpenHandoff.export_trace`, `RecordSupply.ring_returns` and `BoundaryErasure.deliver` specify different endpoints. The admitted export and disposition are missing. |
| Power-on state | Isolated input defined · O | `RegisterVacuum`, `CarrierVacuumSector.range_iff_odd` and `NativeReferenceBackground.stationary_iff` constrain starts. `IsolatedExcitation.occupiedInput` supplies vacuum plus one packet label; the embedded receiver state and the accessible family for general traffic are still missing. |
| Fan-out to readers | Missing · W | The routed-value port, retained record port and comparison flag are typed separately. The EP attachment is open. The [export contract](OVERVIEW.md#component-contracts) describes its required inputs. |
| Per-part energy budget | Missing · K | `CarrierEvents.uniform_activation`, `OpenHandoff.balanced_basis_repair_flag` and `BoundaryErasure.erasing_pays_one` give exact accounts in their scopes. No exhaustive assignment of paid work to the parts exists. |

None of the physical interfaces in this checklist has a complete contract
only in Markdown. The premise documents describe open choices.

### Pillars

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
| Clock | `PMSubstrate.E8Values.Delta_eq` | `Components.trial_slot_margin` · T/J | `CarrierReferenceCycle.clock_closes` | `ClockedRootTrials.quiet_trial_tick` | global only · T | `CarrierReferenceCycle.clock_visits` · T |
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
| NA3 | EP endpoint Margin | This is the declared KAutomaton-to-EP read interface. It has no stored reserve. Accessible writer inputs stay O/W. |
| NA4 | Root and selector pulse Margin | A pulse is an operation on a register. Positive quarter-time is a time bound. Available slack belongs to the clock and register, under T/J. |

These entries remove no clock, traffic, work or occupancy requirement
from the owning component.

### Interactions

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
| D | unspecified · E0 | unspecified · E0 | unspecified · D | unspecified · E0 | unspecified · E0 | unspecified · E0 | unspecified · E0 | unspecified · E0 | `DiagonalReadout.flag_bounds`, `TollAmplitude.wireAmplitude_sq` | unspecified · W [flag versus stored bit] | unspecified · B [flag versus booked export] | `NetCost.expected_count_linear`, `Components.booked_registration_and_erasure_sum` · K | unspecified · W [executed comparison + booked flag] |
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
| O | Split · **EP protocol input** (excitation occupancy/reference record) + KAutomaton background mechanics. **Task B1:** the full map `ChannelVectors.channelCoord` is proved: active-false vector class `sign·2e_axis`; active-true class is the certified triality image (`channelCoord_glueClass`, `channelCoord_injective`, `channelCoord_image_card = 16`). The orientation is fixed by `c ↦ c+1`. **Task P5:** `RecordCoordinates.labelRecord_eq_axis_sign` identifies the record as `(axis=0, sign=1)` on the finite code, but no certified bijection to a D₄ minimal-vector class or sector is present; `SharedReference`/`ColourReference` are not proved equal to `refRecord`. | **Candidate (Task I, hypothesis):** the vacuum is the reference record on both streams everywhere (`bitRingEmbed_background_fixed`), with live label bits replacing one site per ring; colour reference = up record `(false,false)`, lepton reference = neutrino record `(true,false)`. This is not certified. The reference background does not determine the retained request field: `ClockedRootTrials` supplies the request projection separately from the controller background, and no certified map relates them. **Certified for the isolated-excitation sector:** `PMElementaryParticles.IsolatedExcitation.occupiedInput` is the stationary E8 reference plus one 16-slot packet label, and `occupiedInput_admitted` proves the valid two-bank occupancy. The stationary background is a certified family, not a unique vector (`vacuum_stationary`, `vacuum_nonunique`). Accessible occupied ports for general traffic remain free. | Writer population and sampling threshold, basis-loading capacity and trial history counts. The isolated sector fixes the occupancy used by the receiver-trace example. |
| G | Split · **EP protocol input** (retained requests and firing pattern) + KAutomaton receiver rule/guard table **done** | **Reference-background bit rings (Task I, hypothesis).** `bitToll_eq_hamming` reproduces both EP rows from `labelRecord` and the reference records colour `(false,false)` / lepton `(true,false)`. Each record bit runs on its own ring with its own requests: `bitRingEmbed`, `bitRingSum43_eq`, `bitRingTotal43_eq`. With a shared firing pattern, `bitRingTotal43_shared` gives `bitToll ref c * patternSum (firingPattern either r) x0`. Complement symmetry is `tick_complement`/`receiverFlag_complement`; the background alone is fixed (`bitRingEmbed_background_fixed`). Least Toll gives zero for every label (`bitRingTotal43_empty_zero`). This is a hypothesis, not a certified identification. **Record writes are receiver flags.** `IsolatedReceiverTrace.record_step_identity` gives the one-tick record-occupancy change as exchanging `(true,false)` minus `(false,true)` arrivals; `flagCountInt_eq` identifies the receiver flag count with their sum; `record_step_abs_le` and `record_net_le_flagSum` give the one-tick and T-tick bounds. **Unconstrained least Toll selects the empty firing pattern.** `IsolatedReceiverTrace.localizedSum43_eq_zero_iff_empty` gives sum zero iff no site fires; every non-empty 3-ring pattern is at least 14 (`localizedSum43_nonempty_ge_fourteen`). AND selects no `(true,true)` site (`and_zero_iff_no_true_true`); OR selects every site `(false,false)` (`or_zero_iff_all_false`). The 4-ring result is `localizedSumN_four_zero_iff_empty`. The corresponding 5-ring claim is open. No certified result makes a label require receiver registrations; record/readout requirements remain a different ledger. **Requests are independent initial data; no certified relation to the reference background exists.** `ClockedRootTrials.historyCount` takes the controller background and its request projection `requestOf` as separate supplied inputs; `LocalController` and `RingReceiver` retain supplied requests; the native background stores reference values, not requests. Requests are retained and are the remaining controller input for the localized receiver. `IsolatedReceiverTrace.localizedSum43_eq_pattern` gives the 43-tick sum as `patternSum (firingPattern either r) x0`; `firingPattern_ne_iff_mixed` is the clean mixed-request condition; `localized_and_or_differ_iff` says AND and OR differ exactly when their pattern-table entries differ. No certified result forces site-independent requests, so the uniform-request results are conditional on `HomogeneousRequests`: `(false,false)` gives 0 under both rules, `(true,true)` gives 43 under both, and a mixed uniform request gives 0 under AND and 43 under OR. The localized embedding generalizes to `Fin n` for `n = 3,4,5,6`; empty uniform firing gives zero, full uniform firing gives one flag per tick and sum 43. | Executed branch, pulse word, realized crossing and receiver flag. |
| L | Free input · Physical link admission | Specify occupied edges, available link capacity and disturbance, and the through law conditional on earlier crossings. | Route availability and the realized transmission product or restoring weight. |
| Q | Free input · Supply and acceptance | Specify ready-state supply, accepted disturbance and available return capacity at repeat visits. Stationary modes and the population lower bound are conditional on their setup. | Clean visits, restoration and reuse of the writer reference. |
| D | Free input · Physical observation | Specify the detector's read support and its connection to the flags, including whether a controller sees that flag. The conditional flag formula already applies on a supplied state. | Detected or booked flag count and any flag-controlled pulse. |
| K | Split · **EP protocol input** (label Toll and paid event choice) + KAutomaton tariff unit and amplitude conversion | The localized receiver sum is `localizedSum43_eq_pattern` (the `patternSum` table), conditional on the exchange pattern. The record bit-visit column is separate and has no certified common ledger with it. General preparation, crossing, export, reset and reuse tariffs remain free. | Schedule and label Toll, wire amplitude and signed remaining reference cost. |
| W | Split · **EP protocol input** (which label record is read) + KAutomaton receiver-flag computation **done** | On the localized one-excitation field, `receiver_flag_eq` computes the receiver flag from the retained request and the unequal arrivals. `localized_period_registrations_eq` gives the actual 43-tick sum. The record Toll is a separate column, not the receiver sum. | Routed payload and writer sampling, or receiver Toll and hence insertion amplitude. |
| B | Free input · Boundary disposition | Specify which record becomes a booked export, whether it is retained, returned or erased, and the capacity and return connection of that endpoint. | Erased bits per period, restored reference and the erased-bit difference in the reference threshold. |
| J | Free input · Job ownership and contention | Specify simultaneous jobs, contending uses, and equality of state, time and resource for shared service. | Schedule capacity, reuse and incremental maintenance cost. |
| H | **EP protocol input** · Prior and selection family | The localized embedding keeps one state family; the retained request field is enumerated, not a selected prior over histories. `BoundaryErasure.ring_erasure_survivor_eq` returns the normalized supplied prior for an aggregate ensemble. | Aggregate survival for general receiver ensembles. |
| U | **Done for flag identification** · KAutomaton common comparator/record port + EP label record/reference/theta. **Task B1/B3:** the full class map is placed; lepton reference is `+2e_0`, colour reference is the set `{+2e_1,+2e_2,+2e_3}`. A single-site stationary background can carry the lepton vector but not the full colour set; colour needs a composite. No layout reference equality or bit-ring line map is certified. **Task P5:** no certified map from the finite record coordinate to an E8 minimal vector or line; `refRecord` is not identified with `SharedReference`/`ColourReference`, and no E8 line carries the abstract bit ring. | **Reference remains free (Task 3):** `ColourReference.colour_reference_in_payload` and `SharedReference` do not select the bit-ring reference; it enters in `refRecord`/`bitRingEmbed refBit`. **No firing requirement (Task 4):** no certified refresh/maintenance/restoration/occupation theorem forces a receiver registration; the missing link is gap U. **Checkerboard (Task 5, hypothesis):** `tools/bit_ring_checkerboard.py` finds empty firing gapless and full firing gapped with gap `theta`; no certified coherent per-flip amplitude or Lean spectrum theorem. **Gap U: the EP record bit is not certified as a `RingReceiver` record port.** Candidate (Task I, hypothesis): the vacuum is the reference record on both streams; each record bit runs on its own bit ring with its own requests (`bitRingEmbed`, `bitRingTotal43_eq`). The colour reference is the up record `(false,false)`; the lepton reference is the neutrino record `(true,false)`. Complement/background symmetry is `tick_complement`, `receiverFlag_complement`, `bitRingEmbed_background_fixed`; zero-Hamming labels give zero (`bitRingTotal43_hamming_zero`). This removes the Task H encounter scaffolding and resolves the request mismatch only inside the hypothesis: the two bits are separate rings. It is not certified. **Gap U: the EP record bit is not identified with a `RingReceiver` record port.** `WireSchedule.bitToll` and `HeavyFlipRecords.orbit_record_tolls` count `labelRecord` exact flags (`ElectricHeavyRecord.phase_position`/`phase_sector`, `orbitBitPrice`). No certified map identifies that bit with the record-stream Boolean port or record occupancy used by `record_step_identity`. Specify the embedding of admitted traffic, seed, wall and pulse into the heavy writer or static charged insertion, including this identification. | Heavy branch, record reference, lightest offset, tier identification and the physical orders in `1/Δ`. |

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

### Where the earlier questions sit

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

### Joint update and its limit

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
and conditional formulae in the [export contract](OVERVIEW.md#component-contracts). The joint
packet output, effective writer population and paid work can depend
on the supplied packet-bank action and reader attachment.

| Gap | What the lift narrows | What remains |
| --- | --- | --- |
| G | Reversibility and projected guards for both existing core encodings. | Which local conditions and phases enable the actual packet operation. |
| U | FIFO on all 16 packet coordinates when that operation runs. | Identify the wire and EP operator on that joint trace, including carrier crossing and charged insertion. |
| O | Core request fibres and encoded traffic still project exactly. | Accessible joint starts and occupancy, including boundary supply. |
| W | Projected core observables are independent of the bank action. | Which projected or packet-bank output is supplied to the EP reader. |

### Bare-line stabilizer

The mathematical root stabilizer is W(E7), of order 2,903,040.
Allowing the line's sign adds the commuting reflection in the line
root, giving W(E7) × C2, of order 5,806,080. These orders and the
parabolic stabilizer identification are cited facts.
[Green and Xu, §3](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/orthogonal-roots-macdonald-representations-and-quasiparabolic-sets/F6F652B181E985A2D0F5C73662A6FB4A)
and [Winter and van Luijk, §2 and Appendix A](https://link.springer.com/article/10.1007/s00373-021-02315-8).

Lean checks the explicit conjugating root word in
`NodeSymmetry.bare_conjugating_word`. In the highest-root chamber
the first seven E8 simple roots are perpendicular to the highest
root. Their conjugates give the seven generators in this repository's
line coordinates, with the E7 Gram matrix and exact sector action
in `bare_generators_gram` and `bare_sector_coefficients`. The
standard parabolic generator theorem gives exhaustiveness. The
same Lean calculation identifies the direction and the extra sign
reflection in `bare_line_coordinates` and `bare_reverse_direction`.

| Marking | Effect and justification |
| --- | --- |
| Directed edge and stream roles | The sign reflection reverses the positive direction. Keeping the two stream roles fixed removes this operation from the directed encoding. The substrate does not select a stream-role assignment. |
| Scalar phase | A separate phase coordinate supplies no spatial normal. A chosen spatial normal gives the different marked slice groups above. Its identification with the substrate clock is an encoding input. |
| Two named D₄ sectors | Some positive-line stabilizers mix them, as witnessed by `bare_line_mixing_root`. Requiring separate sector actions is a restriction of the carrier encoding. |
| Fixed trial probe | A spatial action moving its reflection axis breaks the fixed-root pulse on either receiver. The marked line subgroup commutes with that probe in `line_probe_equivariant`. |

The largest common action implemented on the directed marked line still
admits AND and OR with hold or FIFO under cellwise packet covariance.
The full bare-line action does not act on that marked encoding, and
no joint Weyl action on its Boolean requests and 16-slot packet follows.
There is no full-group removal of an individual candidate.
-/

namespace PMKAutomaton.Components

open PMAction
open PMConstants
open scoped Matrix

/-- The phase cycle and quiet trial slots are certified. Timing and
scheduling refer to use of this clock by the physical operations. -/
structure Clock (frameMargin clockTariff physicalTiming : Prop) where
  capacity : PMSubstrate.E8Values.Delta = 43
  margin : frameMargin
  map : ∀ t : Fin PMSubstrate.E8Values.Delta, (finRotate PMSubstrate.E8Values.Delta)^[PMSubstrate.E8Values.Delta] t = t
  protocol : ∀ (requests : Bool × Bool) (z : SubstrateReflection.Lattice) (n : ℕ),
    2 ≤ n → n < PMSubstrate.E8Values.Delta →
      ((ClockedRootTrials.tick^[n + 1]) (requests, (z, 0))).2.1 =
        ((ClockedRootTrials.tick^[n]) (requests, (z, 0))).2.1
  toll : clockTariff
  governor : physicalTiming

theorem clock {frameMargin clockTariff physicalTiming : Prop}
    (margin : frameMargin) (toll : clockTariff) (timing : physicalTiming) :
    Clock frameMargin clockTariff physicalTiming where
  capacity := PMSubstrate.E8Values.Delta_eq
  margin := margin
  map := CarrierReferenceCycle.clock_closes
  protocol requests z _ ha hb := ClockedRootTrials.quiet_trial_tick requests z ha hb
  toll := toll
  governor := timing

/-- The two-site port count and the generic two-bank occupation laws
concern their respective encodings. Accessible occupancies are open. -/
structure NodeRegisters (a b : Type*) [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (accessibleOccupancy registerTariff portEnabling : Prop) where
  capacity : Fintype.card (TwoSiteHandoff.Site × ActualRootRepair.Ports) = 8
  margin : accessibleOccupancy
  map : ∀ (e : Equiv.Perm (a × b)) (q : IndependentRegisters.Configuration a b),
    IndependentRegisters.occupied (RegisterControl.extend e q) = IndependentRegisters.occupied q
  protocol : ∀ p : a × b, IndependentRegisters.occupied (IndependentRegisters.encode p) = 2
  toll : registerTariff
  governor : portEnabling

theorem nodeRegisters (a b : Type*) [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {accessibleOccupancy registerTariff portEnabling : Prop}
    (occupancy : accessibleOccupancy) (toll : registerTariff) (enable : portEnabling) :
    NodeRegisters a b accessibleOccupancy registerTariff portEnabling where
  capacity := TwoSiteHandoff.port_count
  margin := occupancy
  map := RegisterControl.occupation_conserved
  protocol := IndependentRegisters.occupied_encode
  toll := toll
  governor := enable

open LocalController in
/-- The finite table concerns retained Boolean rows. Its count supplies
neither their starting support nor a physical guard. -/
structure Controller (requestSupport controlTariff jointGuard : Prop) where
  capacity : Fintype.card EnumeratedRule = 8 ^ (4 * 43)
  margin : requestSupport
  map : ∀ rule : Rule, Function.Bijective (rawTick rule) ↔
    ∀ phase requests, Compatible (rule phase requests)
  protocol : ∀ (rule : Rule) (phase : Phase) (s t : Registers) (x : ℤ),
    s.1 x = t.1 x → (s.2 (x - 1)).1 = (t.2 (x - 1)).1 →
      (s.2 (x + 1)).2 = (t.2 (x + 1)).2 →
      (rawStep rule phase s).1 x = (rawStep rule phase t).1 x ∧
        (rawStep rule phase s).2 x = (rawStep rule phase t).2 x
  toll : controlTariff
  governor : jointGuard

theorem controller {requestSupport controlTariff jointGuard : Prop}
    (support : requestSupport) (toll : controlTariff) (guard : jointGuard) :
    Controller requestSupport controlTariff jointGuard where
  capacity := LocalController.enumerated_rule_count
  margin := support
  map := LocalController.reversible_iff_rows
  protocol := LocalController.radius_one
  toll := toll
  governor := guard

/-- A root word has an exact unitary map and a comparison implementation.
The uniform primitive test leaves other prices and firing open. -/
structure RootPulses (n : Type*) [Fintype n] [DecidableEq n]
    (wordTariff pulseGuard : Prop) where
  capacity : ∀ c, (CarrierEvents.active c).card = 4
  margin : ∀ p : ℝ, 0 < p → p < 1 / 2 → 0 < RootTransferPhase.quarterTime p
  map : ∀ (e : Equiv.Perm n), Function.Involutive e → ∀ p t : ℝ,
    RootTransferPhase.phase e p t ∈ unitary (Matrix n n ℂ)
  protocol : ∀ U : Matrix n n ℂ,
    (BranchPulseContract.program.map (BranchPulseContract.decode U)).prod =
      CoherentComparisonRepair.compare U
  toll : (∀ c, PMSubstrate.NetCost.prob (CarrierEvents.active c) = 1 / 2) ∧ wordTariff
  governor : pulseGuard

theorem rootPulses (n : Type*) [Fintype n] [DecidableEq n] {wordTariff pulseGuard : Prop}
    (toll : wordTariff) (guard : pulseGuard) : RootPulses n wordTariff pulseGuard where
  capacity := CarrierEvents.active_card
  margin := RootTransferPhase.quarterTime_positive
  map := RootTransferPhase.phase_unitary
  protocol := BranchPulseContract.program_correct
  toll := ⟨CarrierEvents.uniform_activation, toll⟩
  governor := guard

/-- The closed-pair return and the mixed flag refer to different certified
tests. The flag tariff and receiver guard remain explicit inputs. -/
structure Receiver (acceptanceMargin bookedComparison receiverGuard : Prop) where
  capacity : Fintype.card (TwoSiteHandoff.Site × ActualRootRepair.Ports) = 8
  margin : acceptanceMargin
  map : ∀ s : TwoSiteHandoff.State Bool, (TwoSiteHandoff.step true)^[4] s = s
  protocol : ∀ (rule : LocalController.Rule) (phase : LocalController.Phase)
    (s : LocalController.Registers) (x : ℤ) (edge : TwoSiteHandoff.State Bool),
    edge 1 = OpenReferenceFlow.streamShift OpenReferenceFlow.line s.2 x →
    (LocalController.rawStep rule phase s).2 x =
      TwoSiteHandoff.step (rule phase (s.1 x).1 (edge 1)) edge 0
  toll : (RingReceiver.receiverFlag false RingReceiver.mixedBasisRing 0 = 0 ∧
    RingReceiver.receiverFlag true RingReceiver.mixedBasisRing 0 = 1) ∧ bookedComparison
  governor : receiverGuard

theorem receiver {acceptanceMargin bookedComparison receiverGuard : Prop}
    (margin : acceptanceMargin) (booked : bookedComparison) (guard : receiverGuard) :
    Receiver acceptanceMargin bookedComparison receiverGuard where
  capacity := TwoSiteHandoff.port_count
  margin := margin
  map := TwoSiteHandoff.exchange_four_returns
  protocol := LocalController.receiver_realisation
  toll := ⟨RingReceiver.mixed_ring_flags, booked⟩
  governor := guard

/-- A line step and a two-stream current law. Available physical edges,
successive crossing conditions and registration are supplied. -/
structure Links (linkCapacity successorMargin crossingTariff admittedCrossings : Prop) where
  capacity : linkCapacity
  margin : successorMargin
  map : ∀ j : ℤ,
    OpenHandoff.address (j + 1) - OpenHandoff.address j = AxisHop.vec OpenHandoff.direction
  protocol : ∀ s : OpenHandoff.State Bool,
    (OpenReferenceFlow.streamShift OpenReferenceFlow.line
      (OpenReferenceFlow.streamShift OpenReferenceFlow.line s) (-1)).2 = (s 1).2
  toll : (∀ w nL nR : ℝ, PMConstants.HandoffAdmittance.leftOutflow w nL nR - nL =
    w * (nR - nL)) ∧ crossingTariff
  governor : admittedCrossings

theorem links {linkCapacity successorMargin crossingTariff admittedCrossings : Prop}
    (capacity : linkCapacity) (margin : successorMargin) (toll : crossingTariff)
    (admission : admittedCrossings) :
    Links linkCapacity successorMargin crossingTariff admittedCrossings where
  capacity := capacity
  margin := margin
  map := OpenHandoff.address_step
  protocol := OpenReferenceFlow.bypass_transmits
  toll := ⟨PMConstants.HandoffAdmittance.node_current, toll⟩
  governor := admission

/-- Wall size, packet slots, reflection and address. The carrier background
and admitted operations are inputs. -/
structure Payload (occupiedPacket packetTariff wallAdmission : Prop) where
  capacity : (∀ c, Fintype.card (CarrierEvents.Carrier c) = 8) ∧
    Function.Bijective PacketGaugeActions.channelIndex
  margin : occupiedPacket
  map : ∀ c, Function.Involutive (CarrierEvents.reflect c)
  protocol : ∀ (g : Fin 3) (b : Bool), ∃! c : Fin 3, g ≠ c ∧ GenerationWalls.side g c = b
  toll : packetTariff
  governor : wallAdmission

theorem payload {occupiedPacket packetTariff wallAdmission : Prop}
    (occupancy : occupiedPacket) (toll : packetTariff) (admission : wallAdmission) :
    Payload occupiedPacket packetTariff wallAdmission where
  capacity := ⟨CarrierEvents.carrier_card, PacketGaugeActions.channel_index_bijective⟩
  margin := occupancy
  map := CarrierEvents.reflection_involutive
  protocol := GenerationWalls.one_class_per_wall
  toll := toll
  governor := admission

/-- The reserved-cell layout and the supplied open restoration trace.
Ready supply and preparation prices are open at the physical visits. -/
structure Reference (supplyMargin preparationTariff renewal : Prop) where
  capacity : ∀ R : Finset (Fin 172), R.Nonempty →
    (∀ S : Finset (Fin 172), S.Nonempty → (Finset.univ \ S).card ≤ (Finset.univ \ R).card) →
    R.card = 1
  margin : CommonResponse.nsq OddReferenceSource.oddReference = 1 ∧ supplyMargin
  map : ∀ L : SharedReference.ReferenceLayout, L.refOf 0 = L.refOf 1
  protocol : ∀ (s : OpenHandoff.State Bool) (accepts : Bool → Prop) (N : ℕ),
    (∀ j : Fin N, accepts (OpenHandoff.run s (j.val + 1) 0).1) ↔
      (∀ j : Fin N, accepts (s (j.val + 1 : ℤ)).2)
  toll : preparationTariff
  governor : renewal

theorem reference {supplyMargin preparationTariff renewal : Prop}
    (margin : supplyMargin) (toll : preparationTariff) (supply : renewal) :
    Reference supplyMargin preparationTariff renewal where
  capacity := SharedReference.reserved_single
  margin := ⟨OddReferenceSource.odd_reference_population, margin⟩
  map := SharedReference.shared
  protocol := OpenHandoff.acceptance_iff_supply
  toll := toll
  governor := supply

/-- The diagonal readout on a supplied state and comparison word.
The detector attachment and bookings remain explicit. -/
structure Readout (n : Type*) [Fintype n] [DecidableEq n]
    (detectorSupport flagBooking detectorWiring : Prop) where
  capacity : detectorSupport
  margin : ∀ x : ℝ, 0 ≤ DiagonalReadout.flag x ∧ DiagonalReadout.flag x ≤ 1
  map : ∀ {H : Matrix n n ℂ} (hH : H.IsHermitian) (q : n → ℝ),
    H = Matrix.diagonal (fun i => (q i : ℂ)) → ∀ (t : ℝ) (φ : n → ℂ),
    CommonResponse.stateFlag (LinkSpectralResponse.HermitianTransport.transport hH t) φ =
      ∑ c, Complex.normSq (φ c) * DiagonalReadout.flag (t * q c)
  protocol : ∀ U : Matrix n n ℂ,
    (BranchPulseContract.program.map (BranchPulseContract.decode U)).prod =
      CoherentComparisonRepair.compare U
  toll : (∀ T : ℝ, PersistenceMechanics.EffectiveAction.attenuationWeight 1 T ^ 2 = PersistenceMechanics.Gibbs.weight 1 T) ∧
    flagBooking
  governor : detectorWiring

theorem readout (n : Type*) [Fintype n] [DecidableEq n]
    {detectorSupport flagBooking detectorWiring : Prop}
    (support : detectorSupport) (booked : flagBooking) (wiring : detectorWiring) :
    Readout n detectorSupport flagBooking detectorWiring where
  capacity := support
  margin := DiagonalReadout.flag_bounds
  map := DiagonalReadout.state_flag
  protocol := BranchPulseContract.program_correct
  toll := ⟨TollAmplitude.wireAmplitude_sq, booked⟩
  governor := wiring

/-- Retained memory and open export. The bound is for an injective
linear reset of the given window. -/
structure Records (n : Type*) [Fintype n] [DecidableEq n] (V A : Type*) [AddCommMonoid A]
    (readyRecords recordTariff consumerPort : Prop) where
  capacity : ∀ (N R : ℕ)
    (T : ((Fin N → n → ℂ) × (Fin R → n → ℂ)) →ₗ[ℂ]
      ((Fin N → n → ℂ) × (Fin R → n → ℂ))),
    Function.Injective T → (∀ inputs, (T (inputs, 0)).1 = 0) →
      N * Fintype.card n ≤ R * Fintype.card n
  margin : readyRecords
  map : ∀ inputs records : List V,
    (RecordTransport.run inputs records).1 ++ (RecordTransport.run inputs records).2 =
      records ++ inputs
  protocol : ∀ (s : OpenHandoff.State V) (N : ℕ) (measure : V → A),
    (∑ d : Fin N, measure (OpenHandoff.run s N (-(d.val : ℤ))).2) =
      ∑ j : Fin N, measure (s (-(j.val + 1 : ℤ))).1
  toll : recordTariff
  governor : consumerPort

theorem records (n : Type*) [Fintype n] [DecidableEq n] (V A : Type*) [AddCommMonoid A]
    {readyRecords recordTariff consumerPort : Prop}
    (ready : readyRecords) (toll : recordTariff) (port : consumerPort) :
    Records n V A readyRecords recordTariff consumerPort where
  capacity := RecordTransport.history_memory_bound
  margin := ready
  map := RecordTransport.stream_conserved
  protocol := OpenHandoff.sum_exported
  toll := toll
  governor := port

/-- Erasure merges exported bits while the retained identity remains
bijective. The boundary contract supplies the booked export, disposition
and return wiring. -/
structure Boundary (I : Type*) (boundaryCapacity exportDisposition : Prop) where
  capacity : Fintype.card BoundaryErasure.Disposition = 3
  margin : boundaryCapacity
  map : ∀ (update : Equiv.Perm I) (exported : I → Option Bool)
    (disposition : I → BoundaryErasure.Disposition),
    Function.Bijective (fun i => (BoundaryErasure.step update i (exported i) (disposition i)).1)
  protocol : ∀ a b : Bool, BoundaryErasure.deliver .erase a = BoundaryErasure.deliver .erase b
  toll : ∀ bit : Bool, BoundaryErasure.erasedBits .erase (some bit) = 1
  governor : exportDisposition

theorem boundary (I : Type*) {boundaryCapacity exportDisposition : Prop}
    (capacity : boundaryCapacity) (disposition : exportDisposition) :
    Boundary I boundaryCapacity exportDisposition where
  capacity := BoundaryErasure.disposition_count
  margin := capacity
  map := BoundaryErasure.identity_bijective
  protocol := BoundaryErasure.erased_bit_merges
  toll := BoundaryErasure.erasing_pays_one
  governor := disposition

/-- Root implementation and minimum cost for supplied jobs. The physical
job set, reserve, prices and arbitration are inputs. -/
structure Maintenance (R : Type*) [DecidableEq R]
    (jobCapacity jobReserve maintenanceTariff arbitration : Prop) where
  capacity : jobCapacity
  margin : jobReserve
  map : ∀ (c : Fin 3) (jr : R → Fin 4) (v : R → CarrierEvents.Carrier c),
    (∀ r, CarrierWeyl.simple c (jr r) (v r) ≠ v r) → ∀ r (s : ReferenceMaintenance.State R),
    RootMaintenance.encodeState c jr v (ReferenceMaintenance.event r s) =
      RootMaintenance.siteEvent c jr r (RootMaintenance.encodeState c jr v s)
  protocol : ∀ (w : R → ℝ), (∀ r, 0 ≤ w r) → ∀ req : Finset R,
    IsLeast {c | ∃ L, RefreshSchedule.admissible req L ∧ RefreshSchedule.cost w L = c}
      (∑ r ∈ req, w r)
  toll : maintenanceTariff
  governor : arbitration

theorem maintenance (R : Type*) [DecidableEq R]
    {jobCapacity jobReserve maintenanceTariff arbitration : Prop}
    (capacity : jobCapacity) (margin : jobReserve) (toll : maintenanceTariff) (arbiter : arbitration) :
    Maintenance R jobCapacity jobReserve maintenanceTariff arbitration where
  capacity := capacity
  margin := margin
  map := RootMaintenance.event_is_root
  protocol := RefreshSchedule.minimal_is_ledger
  toll := toll
  governor := arbiter

/-- Upstream contracts at the EP consumer boundary. The wiring premise
asks what the endpoint reads: routed value and destination, retained
record, or executed comparison with its booked flag. It supplies no
choice between them. -/
structure EPEndpoint (writerPopulation consumerWiring paidRemainder insertionAdmission : Prop) where
  capacity : Function.Bijective PacketGaugeActions.channelIndex
  margin : writerPopulation
  map : ∀ (g : Fin 3) (b : Bool), ∃! c : Fin 3, g ≠ c ∧ GenerationWalls.side g c = b
  protocol : consumerWiring
  toll : (∀ full probeVacancy : Bool,
    Values.outputFlagThreshold full probeVacancy =
      if full then (if probeVacancy then 1 / 2 else 9 / 16) else 3 / 5) ∧
    (∀ full probeVacancy : Bool,
      Values.balancedResetThreshold full probeVacancy =
        if full then (if probeVacancy then 3 / 4 else 27 / 32) else 9 / 10) ∧ paidRemainder
  governor : insertionAdmission

theorem epEndpoint {writerPopulation consumerWiring paidRemainder insertionAdmission : Prop}
    (population : writerPopulation) (wiring : consumerWiring)
    (toll : paidRemainder) (admission : insertionAdmission) :
    EPEndpoint writerPopulation consumerWiring paidRemainder insertionAdmission where
  capacity := PacketGaugeActions.channel_index_bijective
  margin := population
  map := GenerationWalls.one_class_per_wall
  protocol := wiring
  toll := ⟨Values.outputFlagThreshold_eq, Values.balancedResetThreshold_eq, toll⟩
  governor := admission

/-! ## Rates of the certified encodings

A load counts an enabled slot of one Boolean event. A bound on an
encoded slot or port is per instance. It is independent of how many
instances operate together and of the physical duration of a tick.
-/

def phaseLoad (fires : Fin PMSubstrate.E8Values.Delta → Bool) : ℕ :=
  (Finset.univ.filter fun t => fires t = true).card

theorem phaseLoad_le_period (fires : Fin PMSubstrate.E8Values.Delta → Bool) : phaseLoad fires ≤ 43 := by
  simpa [phaseLoad] using Finset.card_filter_le (s := (Finset.univ : Finset (Fin PMSubstrate.E8Values.Delta)))
    (p := fun t => fires t = true)

theorem phaseLoad_full : phaseLoad (fun _ => true) = 43 := by
  simp [phaseLoad]

theorem trial_phaseLoad (requests : Bool × Bool) :
    phaseLoad (ClockedRootTrials.fire requests) = requests.1.toNat + requests.2.toNat := by
  rcases requests with ⟨a, b⟩
  cases a <;> cases b <;> decide +kernel

theorem trial_phaseLoad_le (requests : Bool × Bool) :
    phaseLoad (ClockedRootTrials.fire requests) ≤ 2 := by
  rcases requests with ⟨a, b⟩
  cases a <;> cases b <;> simp [trial_phaseLoad, Bool.toNat]

theorem line_receiver_phaseLoad_le (rule : LocalController.Rule)
    (s : Fin PMSubstrate.E8Values.Delta → LocalController.Registers) (x : ℤ) :
    phaseLoad (fun t => rule t ((s t).1 x).1
      (OpenReferenceFlow.streamShift OpenReferenceFlow.line (s t).2 x)) ≤ 43 :=
  phaseLoad_le_period _

theorem ring_receiver_phaseLoad (either : Bool) (requests : LocalController.Requests) :
    phaseLoad (fun _ => RingReceiver.exchange either requests) =
      if RingReceiver.exchange either requests then 43 else 0 := by
  cases RingReceiver.exchange either requests <;> simp [phaseLoad]

theorem ring_source_neighbour {n : ℕ} (switches : Fin n → Bool) (p : RingReceiver.Slot n) :
    (RingReceiver.portSource switches p).1 = finRotate n p.1 ∨
      (RingReceiver.portSource switches p).1 = (finRotate n).symm p.1 := by
  cases a : p.2 <;> cases b : switches p.1 <;> simp [RingReceiver.portSource, a, b]

theorem fifo_tick_ports (R : ℕ) (input : PacketGaugeActions.Channels → ℂ)
    (records : Fin R → PacketGaugeActions.Channels → ℂ) :
    (∀ a, RecordTransport.tick R
      (fun p => (@Fin.cons R (fun _ => PacketGaugeActions.Channels → ℂ) input records p.1) p.2) (0, a) = (@Fin.snoc R (fun _ => PacketGaugeActions.Channels → ℂ) records input 0) a) ∧
    (∀ a, RecordTransport.tick R
      (fun p => (@Fin.cons R (fun _ => PacketGaugeActions.Channels → ℂ) input records p.1) p.2) (Fin.last R, a) = input a) := by
  exact ⟨RecordTransport.tick_fifo R input records 0,
    fun a => by simpa using RecordTransport.tick_fifo R input records (Fin.last R) a⟩

theorem ring_flag_le_one {n : ℕ} (either : Bool) (s : RingReceiver.State n) (x : Fin n) :
    RingReceiver.receiverFlag either s x ≤ 1 := by
  rw [RingReceiver.receiver_flag_eq]
  split <;> norm_num

theorem erased_bits_le_one (disposition : BoundaryErasure.Disposition) (exported : Option Bool) :
    BoundaryErasure.erasedBits disposition exported ≤ 1 := by
  unfold BoundaryErasure.erasedBits
  split <;> omega

theorem cycle_erased_le_period (disposition : Fin PMSubstrate.E8Values.Delta → BoundaryErasure.Disposition)
    (exported : Fin PMSubstrate.E8Values.Delta → Option Bool) :
    BoundaryErasure.cycleErased disposition exported ≤ 43 := by
  unfold BoundaryErasure.cycleErased
  calc
    _ ≤ ∑ _ : Fin PMSubstrate.E8Values.Delta, (1 : ℕ) :=
      Finset.sum_le_sum (fun t _ => erased_bits_le_one (disposition t) (exported t))
    _ = 43 := by simp

/-! ## Headroom in matching units -/

/-- Empty slots of the isolated trial clock. The all-true requests attain
the worst-case load. These slots are not reserved for concurrent work. -/
theorem trial_slot_margin (requests : Bool × Bool) :
    41 ≤ 43 - phaseLoad (ClockedRootTrials.fire requests) := by
  have := trial_phaseLoad_le requests
  omega

theorem trial_slot_margin_attained :
    43 - phaseLoad (ClockedRootTrials.fire (true, true)) = 41 := by
  rw [trial_phaseLoad]
  rfl

/-- One receiver opportunity at every phase can be used, under either
guard, on the all-true request pair. -/
theorem ring_exchange_full_load (either : Bool) :
    43 - phaseLoad (fun _ => RingReceiver.exchange either (true, true)) = 0 := by
  rw [ring_receiver_phaseLoad]
  cases either <;> rfl

theorem ring_flag_margin_attained :
    1 - RingReceiver.receiverFlag true RingReceiver.mixedBasisRing 0 = 0 := by
  rw [RingReceiver.mixed_ring_flags.2]
  norm_num

/-- The binary port can exhaust its accounting capacity if every input
is booked for erasure. This is an attainable model load. -/
theorem erasure_margin_attained (bits : Fin PMSubstrate.E8Values.Delta → Bool) :
    43 - BoundaryErasure.cycleErased (fun _ => .erase) (fun t => some (bits t)) = 0 := by
  rw [BoundaryErasure.erase_full_cycle, PMSubstrate.E8Values.Delta_eq]

/-! ## Reversible lifts of the retained controller

Cell zero holds the incoming 16-slot packet. The other cells hold the
retained FIFO packets. The fibre map is a supplied operation, with no
default timing or attachment to a receiver guard.
-/

abbrev PacketBank (R : ℕ) := Fin (R + 1) × PacketGaugeActions.Channels → ℂ

def fifoEquiv (R : ℕ) : Equiv.Perm (PacketBank R) where
  toFun f p := f (RecordTransport.shift R p)
  invFun f p := f ((RecordTransport.shift R).symm p)
  left_inv f := by ext p; simp
  right_inv f := by ext p; simp

theorem fifoEquiv_eq_tick (R : ℕ) (bank : PacketBank R) :
    fifoEquiv R bank = RecordTransport.tick R bank := by
  funext p
  rcases p with ⟨i, a⟩
  exact (RecordTransport.tick_apply R bank i a).symm

def jointTick {I : Type*} {R : ℕ} (core : I → I)
    (packet : I → Equiv.Perm (PacketBank R)) (s : I × PacketBank R) : I × PacketBank R :=
  (core s.1, packet s.1 s.2)

theorem joint_core_iterate {I : Type*} {R : ℕ} (core : I → I)
    (packet : I → Equiv.Perm (PacketBank R)) (s : I × PacketBank R) (n : ℕ) :
    ((jointTick core packet)^[n] s).1 = core^[n] s.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact congrArg core ih

theorem joint_bijective_iff {I : Type*} {R : ℕ} (core : I → I)
    (packet : I → Equiv.Perm (PacketBank R)) :
    Function.Bijective (jointTick core packet) ↔ Function.Bijective core := by
  constructor
  · intro hj
    constructor
    · intro x y h
      exact congrArg Prod.fst (hj.1 (a₁ := (x, (packet x).symm 0))
        (a₂ := (y, (packet y).symm 0)) (by simp [jointTick, h]))
    · intro y
      obtain ⟨s, hs⟩ := hj.2 (y, 0)
      exact ⟨s.1, congrArg Prod.fst hs⟩
  · intro h
    let e := Equiv.ofBijective core h
    exact ((Equiv.prodCongrRight packet).trans (e.prodCongr (Equiv.refl _))).bijective

/-- Every bijective step over a fixed reversible core has exactly one
packet-bank permutation at each core input. This is a classification
of the lifts, before adding any physical locality or firing contract. -/
theorem joint_lift_iff {I : Type*} {R : ℕ} (core : Equiv.Perm I)
    (tick : I × PacketBank R → I × PacketBank R)
    (hc : ∀ s, (tick s).1 = core s.1) :
    Function.Bijective tick ↔ ∃! packet, tick = jointTick core packet := by
  constructor
  · intro ht
    have hf (x : I) : Function.Bijective (fun bank => (tick (x, bank)).2) := by
      constructor
      · intro a b h
        exact congrArg Prod.snd (ht.1 (Prod.ext
          ((hc (x, a)).trans (hc (x, b)).symm) h))
      · intro out
        obtain ⟨⟨y, bank⟩, hy⟩ := ht.2 (core x, out)
        have hyx : y = x := core.injective ((hc (y, bank)).symm.trans (congrArg Prod.fst hy))
        subst y
        exact ⟨bank, congrArg Prod.snd hy⟩
    let packet (x : I) : Equiv.Perm (PacketBank R) := Equiv.ofBijective _ (hf x)
    have heq : tick = jointTick core packet :=
      funext fun s => Prod.ext (hc s) rfl
    refine ⟨packet, heq, ?_⟩
    intro other ho
    funext x
    apply Equiv.ext
    intro bank
    have h := congrFun (ho.symm.trans heq) (x, bank)
    exact congrArg Prod.snd h
  · rintro ⟨packet, rfl, _⟩
    exact (joint_bijective_iff _ _).2 core.bijective

theorem joint_line_bijective_iff {R : ℕ} (rule : LocalController.Rule)
    (packet : LocalController.State → Equiv.Perm (PacketBank R)) :
    Function.Bijective (jointTick (LocalController.rawTick rule) packet) ↔
      ∀ phase requests, LocalController.Compatible (rule phase requests) :=
  (joint_bijective_iff _ _).trans (LocalController.reversible_iff_rows rule)

theorem joint_ring_bijective {n R : ℕ} (either : Bool)
    (packet : RingReceiver.State n → Equiv.Perm (PacketBank R)) :
    Function.Bijective (jointTick (RingReceiver.tick n either) packet) :=
  (joint_bijective_iff _ _).mpr (RingReceiver.tick_bijective n either)

theorem joint_fifo_restriction {I : Type*} (R : ℕ) (core : I → I)
    (s : I × PacketBank R) :
    (jointTick core (fun _ => fifoEquiv R) s).2 = RecordTransport.tick R s.2 :=
  fifoEquiv_eq_tick R s.2

/-- Two stipulated factor projections would force the independent
product. The core projection alone implies no packet projection. -/
theorem joint_fixed_projections {I : Type*} {R : ℕ} (core : I → I)
    (packet : PacketBank R → PacketBank R)
    (tick : I × PacketBank R → I × PacketBank R)
    (hc : ∀ s, (tick s).1 = core s.1) (hp : ∀ s, (tick s).2 = packet s.2) :
    tick = Prod.map core packet := by
  funext s
  exact Prod.ext (hc s) (hp s)

theorem joint_two_fifo_placements_differ {I : Type*} (core : I → I)
    (x : I) (a : PacketGaugeActions.Channels) :
    ∃ bank : PacketBank 1,
      (jointTick core (fun _ => fifoEquiv 1) (x, bank)).2 (0, a) ≠
      (jointTick core (fun _ => Equiv.refl _) (x, bank)).2 (0, a) := by
  refine ⟨fun p => if p.1 = 0 then 0 else 1, ?_⟩
  change (if finRotate 2 (0 : Fin 2) = 0 then (0 : ℂ) else 1) ≠
    (if (0 : Fin 2) = 0 then (0 : ℂ) else 1)
  simp

theorem joint_boundary_identity {I : Type*} {R : ℕ} (core : Equiv.Perm I)
    (packet : I → Equiv.Perm (PacketBank R))
    (exported : I × PacketBank R → Option Bool)
    (disposition : I × PacketBank R → BoundaryErasure.Disposition) :
    Function.Bijective (fun s =>
      (BoundaryErasure.step
        ((Equiv.prodCongrRight packet).trans (core.prodCongr (Equiv.refl _)))
        s (exported s) (disposition s)).1) :=
  BoundaryErasure.identity_bijective _ exported disposition

/-! ## Local observations of a certified receiver -/

theorem ring_observations_local {n : ℕ} (either : Bool)
    (s t : RingReceiver.State n) (x : Fin n)
    (hq : s.2.1 x = t.2.1 x)
    (hl : (s.2.2.2 ((finRotate n).symm x)).1 = (t.2.2.2 ((finRotate n).symm x)).1)
    (hr : (s.2.2.2 (finRotate n x)).2 = (t.2.2.2 (finRotate n x)).2) :
    (RingReceiver.tick n either s).2.2.2 x = (RingReceiver.tick n either t).2.2.2 x ∧
      RingReceiver.receiverFlag either s x = RingReceiver.receiverFlag either t x := by
  have ha : RingReceiver.arrivals s.2.2.2 x = RingReceiver.arrivals t.2.2.2 x :=
    Prod.ext hl hr
  constructor
  · rw [RingReceiver.tick_ports, RingReceiver.tick_ports, hq, ha]
  · rw [RingReceiver.receiver_flag_eq, RingReceiver.receiver_flag_eq, hq, ha]

/-! ## Accounting for supplied registrations and exported erasures -/

/-- Partition the booked unit registrations by their supplied owner.
The erased bits are additional booked erasure events on this trace.
A read and a later erasure are separate operations. This equality
does not identify which visits physically register. -/
theorem booked_registration_and_erasure_sum {Ω C : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype C] [DecidableEq C] {k : ℕ} (owner : Fin k → C) (events : Fin k → Finset Ω)
    (disposition : Fin PMSubstrate.E8Values.Delta → BoundaryErasure.Disposition) (exported : Fin PMSubstrate.E8Values.Delta → Option Bool) :
    (∑ c : C, ∑ i ∈ Finset.univ.filter (fun i => owner i = c),
      PMSubstrate.NetCost.prob (events i)) +
      (BoundaryErasure.cycleErased disposition exported : ℝ) =
    PMSubstrate.NetCost.expectedCost 1 events +
      (BoundaryErasure.cycleErased disposition exported : ℝ) := by
  rw [PMSubstrate.NetCost.expected_count_linear, one_mul, Finset.sum_fiberwise]

/-- The tagged open symmetry lifts if the two rules use the same
packet-bank action on the common core trace. -/
theorem joint_tagged_ticks_equal {R : ℕ}
    (packet : LocalController.State → Equiv.Perm (PacketBank R))
    (s : LocalController.State × PacketBank R) (hs : LocalController.CentreTagged s.1)
    (n : ℕ) :
    ((jointTick (LocalController.rawTick LocalController.exchangeOnBoth) packet)^[n] s) =
      ((jointTick (LocalController.rawTick LocalController.exchangeOnEither) packet)^[n] s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · rw [joint_core_iterate, joint_core_iterate]
      exact LocalController.tagged_ticks_equal s.1 hs (n + 1)
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rfl

/-! ## Weyl stabilizers in a marked D₄ sector

The signed frame is recorded in lookup order. Its action is on integer
sector coordinates. The other sector and the scalar clock phase are
separate from the active edge. Reflections are the eight certified
embedded simple roots, four per sector.
-/

namespace NodeSymmetry

set_option maxRecDepth 16000

open Finset

abbrev Frame := (Fin 4 → Fin 4) × (Fin 4 → Bool)

def d4 (f : Frame) : Prop :=
  Function.Injective f.1 ∧ (univ.filter fun i => f.2 i = true).card % 2 = 0

instance (f : Frame) : Decidable (d4 f) := inferInstanceAs (Decidable (_ ∧ _))

def act (f : Frame) (v : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun i => if f.2 i then -v (f.1 i) else v (f.1 i)

def identity : Frame := (id, fun _ => false)

def comp (f g : Frame) : Frame :=
  (g.1 ∘ f.1, fun i => Bool.xor (f.2 i) (g.2 (f.1 i)))

theorem act_comp (f g : Frame) (v : Fin 4 → ℤ) :
    act (comp f g) v = act f (act g v) := by
  funext i
  unfold act comp
  cases hf : f.2 i <;> cases hg : g.2 (f.1 i) <;> simp [hf, hg]

def simpleFrame : Fin 4 → Frame := ![
  (Equiv.swap 0 1, fun _ => false),
  (Equiv.swap 1 2, fun _ => false),
  (Equiv.swap 2 3, fun _ => false),
  (Equiv.swap 2 3, fun i => i = 2 || i = 3)]

theorem simpleFrame_root (j : Fin 4) (v : Fin 4 → ℤ) :
    act (simpleFrame j) v =
      PMSubstrate.ChannelSymmetry.refl (PMSubstrate.ChannelSymmetry.simple j) v := by
  funext i
  fin_cases j <;> fin_cases i <;>
    norm_num [act, simpleFrame, PMSubstrate.ChannelSymmetry.refl,
      PMSubstrate.ChannelSymmetry.simple, PMSubstrate.ChannelSymmetry.dot4,
      Fin.sum_univ_four, Equiv.swap_apply_def]

theorem simpleFrame_carrier (c : Fin 3) (j : Fin 4) (v : CarrierEvents.Carrier c) :
    CarrierEvents.vector (CarrierWeyl.simple c j v) = act (simpleFrame j) (CarrierEvents.vector v) :=
  (CarrierWeyl.simple_is_root c j v).trans (simpleFrame_root _ _).symm

theorem simpleFrame_substrate (s t : Bool) (j : Fin 4) (w : SubstrateWeylRoots.Lattice) :
    SubstrateWeylRoots.sector t (SubstrateWeylRoots.coordinates s j w) =
      if t = s then act (simpleFrame j) (SubstrateWeylRoots.sector t w)
      else SubstrateWeylRoots.sector t w := by
  rw [simpleFrame_root]
  exact SubstrateWeylRoots.sector_intertwines s t j w

/-- The line fixes the positive root. The axis hop fixes the positive
axis. The slice also fixes the oriented clock normal. -/
inductive Link
  | sector
  | line
  | axis
  | slice

def preserves : Link → Frame → Prop
  | .sector, _ => True
  | .line, f => act f (AxisHop.vec OpenHandoff.direction) = AxisHop.vec OpenHandoff.direction
  | .axis, f => act f (AxisHop.epsAxis 0) = AxisHop.epsAxis 0
  | .slice, f => act f (AxisHop.epsAxis 0) = AxisHop.epsAxis 0 ∧ act f (AxisHop.epsAxis 3) = AxisHop.epsAxis 3

instance (l : Link) (f : Frame) : Decidable (preserves l f) := by
  cases l <;> unfold preserves <;> infer_instance

def stabilizer (l : Link) : Finset Frame :=
  univ.filter fun f => d4 f ∧ preserves l f

/-! ### Cached stabilizer closures

`stabilizer l` is the same finite set in every later proof.  Each literal is
computed once, and `decide +kernel` on the literal is cheap, so the later
declarations no longer recompute the filter. -/

/-- Cached literal for `stabilizer .sector`. -/
def stabilizerSectorLit : Finset Frame := [
  (![0, 1, 2, 3], ![false, false, false, false]),
  (![0, 1, 2, 3], ![true, true, false, false]),
  (![0, 1, 2, 3], ![true, false, true, false]),
  (![0, 1, 2, 3], ![false, true, true, false]),
  (![0, 1, 2, 3], ![true, false, false, true]),
  (![0, 1, 2, 3], ![false, true, false, true]),
  (![0, 1, 2, 3], ![false, false, true, true]),
  (![0, 1, 2, 3], ![true, true, true, true]),
  (![1, 0, 2, 3], ![false, false, false, false]),
  (![1, 0, 2, 3], ![true, true, false, false]),
  (![1, 0, 2, 3], ![true, false, true, false]),
  (![1, 0, 2, 3], ![false, true, true, false]),
  (![1, 0, 2, 3], ![true, false, false, true]),
  (![1, 0, 2, 3], ![false, true, false, true]),
  (![1, 0, 2, 3], ![false, false, true, true]),
  (![1, 0, 2, 3], ![true, true, true, true]),
  (![2, 1, 0, 3], ![false, false, false, false]),
  (![2, 1, 0, 3], ![true, true, false, false]),
  (![2, 1, 0, 3], ![true, false, true, false]),
  (![2, 1, 0, 3], ![false, true, true, false]),
  (![2, 1, 0, 3], ![true, false, false, true]),
  (![2, 1, 0, 3], ![false, true, false, true]),
  (![2, 1, 0, 3], ![false, false, true, true]),
  (![2, 1, 0, 3], ![true, true, true, true]),
  (![1, 2, 0, 3], ![false, false, false, false]),
  (![1, 2, 0, 3], ![true, true, false, false]),
  (![1, 2, 0, 3], ![true, false, true, false]),
  (![1, 2, 0, 3], ![false, true, true, false]),
  (![1, 2, 0, 3], ![true, false, false, true]),
  (![1, 2, 0, 3], ![false, true, false, true]),
  (![1, 2, 0, 3], ![false, false, true, true]),
  (![1, 2, 0, 3], ![true, true, true, true]),
  (![2, 0, 1, 3], ![false, false, false, false]),
  (![2, 0, 1, 3], ![true, true, false, false]),
  (![2, 0, 1, 3], ![true, false, true, false]),
  (![2, 0, 1, 3], ![false, true, true, false]),
  (![2, 0, 1, 3], ![true, false, false, true]),
  (![2, 0, 1, 3], ![false, true, false, true]),
  (![2, 0, 1, 3], ![false, false, true, true]),
  (![2, 0, 1, 3], ![true, true, true, true]),
  (![0, 2, 1, 3], ![false, false, false, false]),
  (![0, 2, 1, 3], ![true, true, false, false]),
  (![0, 2, 1, 3], ![true, false, true, false]),
  (![0, 2, 1, 3], ![false, true, true, false]),
  (![0, 2, 1, 3], ![true, false, false, true]),
  (![0, 2, 1, 3], ![false, true, false, true]),
  (![0, 2, 1, 3], ![false, false, true, true]),
  (![0, 2, 1, 3], ![true, true, true, true]),
  (![3, 2, 1, 0], ![false, false, false, false]),
  (![3, 2, 1, 0], ![true, true, false, false]),
  (![3, 2, 1, 0], ![true, false, true, false]),
  (![3, 2, 1, 0], ![false, true, true, false]),
  (![3, 2, 1, 0], ![true, false, false, true]),
  (![3, 2, 1, 0], ![false, true, false, true]),
  (![3, 2, 1, 0], ![false, false, true, true]),
  (![3, 2, 1, 0], ![true, true, true, true]),
  (![2, 3, 1, 0], ![false, false, false, false]),
  (![2, 3, 1, 0], ![true, true, false, false]),
  (![2, 3, 1, 0], ![true, false, true, false]),
  (![2, 3, 1, 0], ![false, true, true, false]),
  (![2, 3, 1, 0], ![true, false, false, true]),
  (![2, 3, 1, 0], ![false, true, false, true]),
  (![2, 3, 1, 0], ![false, false, true, true]),
  (![2, 3, 1, 0], ![true, true, true, true]),
  (![2, 1, 3, 0], ![false, false, false, false]),
  (![2, 1, 3, 0], ![true, true, false, false]),
  (![2, 1, 3, 0], ![true, false, true, false]),
  (![2, 1, 3, 0], ![false, true, true, false]),
  (![2, 1, 3, 0], ![true, false, false, true]),
  (![2, 1, 3, 0], ![false, true, false, true]),
  (![2, 1, 3, 0], ![false, false, true, true]),
  (![2, 1, 3, 0], ![true, true, true, true]),
  (![3, 1, 2, 0], ![false, false, false, false]),
  (![3, 1, 2, 0], ![true, true, false, false]),
  (![3, 1, 2, 0], ![true, false, true, false]),
  (![3, 1, 2, 0], ![false, true, true, false]),
  (![3, 1, 2, 0], ![true, false, false, true]),
  (![3, 1, 2, 0], ![false, true, false, true]),
  (![3, 1, 2, 0], ![false, false, true, true]),
  (![3, 1, 2, 0], ![true, true, true, true]),
  (![1, 3, 2, 0], ![false, false, false, false]),
  (![1, 3, 2, 0], ![true, true, false, false]),
  (![1, 3, 2, 0], ![true, false, true, false]),
  (![1, 3, 2, 0], ![false, true, true, false]),
  (![1, 3, 2, 0], ![true, false, false, true]),
  (![1, 3, 2, 0], ![false, true, false, true]),
  (![1, 3, 2, 0], ![false, false, true, true]),
  (![1, 3, 2, 0], ![true, true, true, true]),
  (![1, 2, 3, 0], ![false, false, false, false]),
  (![1, 2, 3, 0], ![true, true, false, false]),
  (![1, 2, 3, 0], ![true, false, true, false]),
  (![1, 2, 3, 0], ![false, true, true, false]),
  (![1, 2, 3, 0], ![true, false, false, true]),
  (![1, 2, 3, 0], ![false, true, false, true]),
  (![1, 2, 3, 0], ![false, false, true, true]),
  (![1, 2, 3, 0], ![true, true, true, true]),
  (![3, 0, 1, 2], ![false, false, false, false]),
  (![3, 0, 1, 2], ![true, true, false, false]),
  (![3, 0, 1, 2], ![true, false, true, false]),
  (![3, 0, 1, 2], ![false, true, true, false]),
  (![3, 0, 1, 2], ![true, false, false, true]),
  (![3, 0, 1, 2], ![false, true, false, true]),
  (![3, 0, 1, 2], ![false, false, true, true]),
  (![3, 0, 1, 2], ![true, true, true, true]),
  (![0, 3, 1, 2], ![false, false, false, false]),
  (![0, 3, 1, 2], ![true, true, false, false]),
  (![0, 3, 1, 2], ![true, false, true, false]),
  (![0, 3, 1, 2], ![false, true, true, false]),
  (![0, 3, 1, 2], ![true, false, false, true]),
  (![0, 3, 1, 2], ![false, true, false, true]),
  (![0, 3, 1, 2], ![false, false, true, true]),
  (![0, 3, 1, 2], ![true, true, true, true]),
  (![0, 1, 3, 2], ![false, false, false, false]),
  (![0, 1, 3, 2], ![true, true, false, false]),
  (![0, 1, 3, 2], ![true, false, true, false]),
  (![0, 1, 3, 2], ![false, true, true, false]),
  (![0, 1, 3, 2], ![true, false, false, true]),
  (![0, 1, 3, 2], ![false, true, false, true]),
  (![0, 1, 3, 2], ![false, false, true, true]),
  (![0, 1, 3, 2], ![true, true, true, true]),
  (![3, 1, 0, 2], ![false, false, false, false]),
  (![3, 1, 0, 2], ![true, true, false, false]),
  (![3, 1, 0, 2], ![true, false, true, false]),
  (![3, 1, 0, 2], ![false, true, true, false]),
  (![3, 1, 0, 2], ![true, false, false, true]),
  (![3, 1, 0, 2], ![false, true, false, true]),
  (![3, 1, 0, 2], ![false, false, true, true]),
  (![3, 1, 0, 2], ![true, true, true, true]),
  (![1, 3, 0, 2], ![false, false, false, false]),
  (![1, 3, 0, 2], ![true, true, false, false]),
  (![1, 3, 0, 2], ![true, false, true, false]),
  (![1, 3, 0, 2], ![false, true, true, false]),
  (![1, 3, 0, 2], ![true, false, false, true]),
  (![1, 3, 0, 2], ![false, true, false, true]),
  (![1, 3, 0, 2], ![false, false, true, true]),
  (![1, 3, 0, 2], ![true, true, true, true]),
  (![1, 0, 3, 2], ![false, false, false, false]),
  (![1, 0, 3, 2], ![true, true, false, false]),
  (![1, 0, 3, 2], ![true, false, true, false]),
  (![1, 0, 3, 2], ![false, true, true, false]),
  (![1, 0, 3, 2], ![true, false, false, true]),
  (![1, 0, 3, 2], ![false, true, false, true]),
  (![1, 0, 3, 2], ![false, false, true, true]),
  (![1, 0, 3, 2], ![true, true, true, true]),
  (![3, 0, 2, 1], ![false, false, false, false]),
  (![3, 0, 2, 1], ![true, true, false, false]),
  (![3, 0, 2, 1], ![true, false, true, false]),
  (![3, 0, 2, 1], ![false, true, true, false]),
  (![3, 0, 2, 1], ![true, false, false, true]),
  (![3, 0, 2, 1], ![false, true, false, true]),
  (![3, 0, 2, 1], ![false, false, true, true]),
  (![3, 0, 2, 1], ![true, true, true, true]),
  (![0, 3, 2, 1], ![false, false, false, false]),
  (![0, 3, 2, 1], ![true, true, false, false]),
  (![0, 3, 2, 1], ![true, false, true, false]),
  (![0, 3, 2, 1], ![false, true, true, false]),
  (![0, 3, 2, 1], ![true, false, false, true]),
  (![0, 3, 2, 1], ![false, true, false, true]),
  (![0, 3, 2, 1], ![false, false, true, true]),
  (![0, 3, 2, 1], ![true, true, true, true]),
  (![0, 2, 3, 1], ![false, false, false, false]),
  (![0, 2, 3, 1], ![true, true, false, false]),
  (![0, 2, 3, 1], ![true, false, true, false]),
  (![0, 2, 3, 1], ![false, true, true, false]),
  (![0, 2, 3, 1], ![true, false, false, true]),
  (![0, 2, 3, 1], ![false, true, false, true]),
  (![0, 2, 3, 1], ![false, false, true, true]),
  (![0, 2, 3, 1], ![true, true, true, true]),
  (![3, 2, 0, 1], ![false, false, false, false]),
  (![3, 2, 0, 1], ![true, true, false, false]),
  (![3, 2, 0, 1], ![true, false, true, false]),
  (![3, 2, 0, 1], ![false, true, true, false]),
  (![3, 2, 0, 1], ![true, false, false, true]),
  (![3, 2, 0, 1], ![false, true, false, true]),
  (![3, 2, 0, 1], ![false, false, true, true]),
  (![3, 2, 0, 1], ![true, true, true, true]),
  (![2, 3, 0, 1], ![false, false, false, false]),
  (![2, 3, 0, 1], ![true, true, false, false]),
  (![2, 3, 0, 1], ![true, false, true, false]),
  (![2, 3, 0, 1], ![false, true, true, false]),
  (![2, 3, 0, 1], ![true, false, false, true]),
  (![2, 3, 0, 1], ![false, true, false, true]),
  (![2, 3, 0, 1], ![false, false, true, true]),
  (![2, 3, 0, 1], ![true, true, true, true]),
  (![2, 0, 3, 1], ![false, false, false, false]),
  (![2, 0, 3, 1], ![true, true, false, false]),
  (![2, 0, 3, 1], ![true, false, true, false]),
  (![2, 0, 3, 1], ![false, true, true, false]),
  (![2, 0, 3, 1], ![true, false, false, true]),
  (![2, 0, 3, 1], ![false, true, false, true]),
  (![2, 0, 3, 1], ![false, false, true, true]),
  (![2, 0, 3, 1], ![true, true, true, true])].toFinset

theorem stabilizer_sector_eq : stabilizer .sector = stabilizerSectorLit := by decide +kernel

/-- Cached literal for `stabilizer .line`. -/
def stabilizerLineLit : Finset Frame := [
  (![0, 1, 2, 3], ![false, false, false, false]),
  (![0, 1, 2, 3], ![false, false, true, true]),
  (![1, 0, 2, 3], ![false, false, false, false]),
  (![1, 0, 2, 3], ![false, false, true, true]),
  (![0, 1, 3, 2], ![false, false, false, false]),
  (![0, 1, 3, 2], ![false, false, true, true]),
  (![1, 0, 3, 2], ![false, false, false, false]),
  (![1, 0, 3, 2], ![false, false, true, true])].toFinset

theorem stabilizer_line_eq : stabilizer .line = stabilizerLineLit := by decide +kernel

/-- Cached literal for `stabilizer .axis`. -/
def stabilizerAxisLit : Finset Frame := [
  (![0, 1, 2, 3], ![false, false, false, false]),
  (![0, 1, 2, 3], ![false, true, true, false]),
  (![0, 1, 2, 3], ![false, true, false, true]),
  (![0, 1, 2, 3], ![false, false, true, true]),
  (![0, 2, 1, 3], ![false, false, false, false]),
  (![0, 2, 1, 3], ![false, true, true, false]),
  (![0, 2, 1, 3], ![false, true, false, true]),
  (![0, 2, 1, 3], ![false, false, true, true]),
  (![0, 3, 1, 2], ![false, false, false, false]),
  (![0, 3, 1, 2], ![false, true, true, false]),
  (![0, 3, 1, 2], ![false, true, false, true]),
  (![0, 3, 1, 2], ![false, false, true, true]),
  (![0, 1, 3, 2], ![false, false, false, false]),
  (![0, 1, 3, 2], ![false, true, true, false]),
  (![0, 1, 3, 2], ![false, true, false, true]),
  (![0, 1, 3, 2], ![false, false, true, true]),
  (![0, 3, 2, 1], ![false, false, false, false]),
  (![0, 3, 2, 1], ![false, true, true, false]),
  (![0, 3, 2, 1], ![false, true, false, true]),
  (![0, 3, 2, 1], ![false, false, true, true]),
  (![0, 2, 3, 1], ![false, false, false, false]),
  (![0, 2, 3, 1], ![false, true, true, false]),
  (![0, 2, 3, 1], ![false, true, false, true]),
  (![0, 2, 3, 1], ![false, false, true, true])].toFinset

theorem stabilizer_axis_eq : stabilizer .axis = stabilizerAxisLit := by decide +kernel

/-- Cached literal for `stabilizer .slice`. -/
def stabilizerSliceLit : Finset Frame := [
  (![0, 1, 2, 3], ![false, false, false, false]),
  (![0, 1, 2, 3], ![false, true, true, false]),
  (![0, 2, 1, 3], ![false, false, false, false]),
  (![0, 2, 1, 3], ![false, true, true, false])].toFinset

theorem stabilizer_slice_eq : stabilizer .slice = stabilizerSliceLit := by decide +kernel

/-- Finite enumeration in the marked active D₄ factor. -/
theorem stabilizer_orders :
    (stabilizer .sector).card = 192 ∧ (stabilizer .line).card = 8 ∧
      (stabilizer .axis).card = 24 ∧ (stabilizer .slice).card = 4 := by
  rw [stabilizer_sector_eq, stabilizer_line_eq, stabilizer_axis_eq, stabilizer_slice_eq]
  decide +kernel

def wordFrame : List (Fin 4) → Frame
  | [] => identity
  | j :: w => comp (simpleFrame j) (wordFrame w)

def generatorWords : Link → List (List (Fin 4))
  | .sector => [[0], [1], [2], [3]]
  | .line => [[0], [2], [3]]
  | .axis => [[1], [2], [3]]
  | .slice => [[1], [2, 1, 2, 3, 1, 2]]

/-- Enumeration of products of the proposed generators up to a depth. -/
def products (gs : Finset Frame) : ℕ → Finset Frame
  | 0 => {identity}
  | n + 1 =>
    let reached := products gs n
    reached ∪ (gs ×ˢ reached).image (fun p => comp p.1 p.2)

theorem line_generators :
    products ((generatorWords .line).toFinset.image wordFrame) 3 = stabilizer .line := by
  rw [stabilizer_line_eq]
  decide +kernel

theorem axis_generators :
    products ((generatorWords .axis).toFinset.image wordFrame) 6 = stabilizer .axis := by
  rw [stabilizer_axis_eq]
  decide +kernel

theorem slice_generators :
    products ((generatorWords .slice).toFinset.image wordFrame) 2 = stabilizer .slice := by
  rw [stabilizer_slice_eq]
  decide +kernel

def unsignedFrames : Finset Frame :=
  (stabilizer .sector).filter fun f => f.2 = fun _ => false

def diagonalFrames : Finset Frame :=
  (stabilizer .sector).filter fun f => f.1 = id

theorem unsigned_generators :
    products (([[0], [1], [2]] : List (List (Fin 4))).toFinset.image wordFrame) 6 =
      unsignedFrames := by
  rw [unsignedFrames, stabilizer_sector_eq]
  decide +kernel

theorem diagonal_generators :
    products (([[2, 3], [1, 2, 3, 1], [0, 1, 2, 3, 1, 0]] :
      List (List (Fin 4))).toFinset.image wordFrame) 3 = diagonalFrames := by
  rw [diagonalFrames, stabilizer_sector_eq]
  decide +kernel

theorem sector_factor (f : Frame) (hf : f ∈ stabilizer .sector) :
    (f.1, fun _ => false) ∈ unsignedFrames ∧ (id, f.2) ∈ diagonalFrames ∧
      comp (id, f.2) (f.1, fun _ => false) = f := by
  have hd := (mem_filter.mp hf).2.1
  refine ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ⟨hd.1, by simp⟩, trivial⟩, rfl⟩,
    mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ⟨fun _ _ h => h, hd.2⟩, trivial⟩, rfl⟩, ?_⟩
  apply Prod.ext
  · rfl
  · funext i
    simp [comp]

/-- The line subgroup preserves the unoriented probe reflection root.
The sliced axis subgroup need not preserve it. -/
theorem line_preserves_probe :
    ∀ f ∈ stabilizer .line,
      act f (PMSubstrate.ChannelSymmetry.simple 0) = PMSubstrate.ChannelSymmetry.simple 0 ∨
      act f (PMSubstrate.ChannelSymmetry.simple 0) = -PMSubstrate.ChannelSymmetry.simple 0 := by
  rw [stabilizer_line_eq]
  decide +kernel

theorem slice_can_move_probe :
    simpleFrame 1 ∈ stabilizer .slice ∧
      act (simpleFrame 1) (PMSubstrate.ChannelSymmetry.simple 0) ≠
        PMSubstrate.ChannelSymmetry.simple 0 ∧
      act (simpleFrame 1) (PMSubstrate.ChannelSymmetry.simple 0) ≠
        -PMSubstrate.ChannelSymmetry.simple 0 := by
  rw [stabilizer_slice_eq]
  decide +kernel

/-- A uniform degree of freedom in the unmarked sector is independent
of the edge marking. Count pairs in the two embedded signed frames. -/
theorem paired_orders :
    ((stabilizer .line) ×ˢ (stabilizer .sector)).card = 1536 ∧
    ((stabilizer .axis) ×ˢ (stabilizer .sector)).card = 4608 ∧
    ((stabilizer .slice) ×ˢ (stabilizer .sector)).card = 768 := by
  obtain ⟨hs, hl, ha, hc⟩ := stabilizer_orders
  simp [card_product, hs, hl, ha, hc]

private theorem probe_fix_pair : ∀ f, d4 f → preserves .axis f →
    ((act f (PMSubstrate.ChannelSymmetry.simple 0) = PMSubstrate.ChannelSymmetry.simple 0 ∨
      act f (PMSubstrate.ChannelSymmetry.simple 0) = -PMSubstrate.ChannelSymmetry.simple 0) ↔
        act f (AxisHop.epsAxis 1) = AxisHop.epsAxis 1) := by
  have h : ∀ f ∈ stabilizer .axis,
      ((act f (PMSubstrate.ChannelSymmetry.simple 0) = PMSubstrate.ChannelSymmetry.simple 0 ∨
        act f (PMSubstrate.ChannelSymmetry.simple 0) = -PMSubstrate.ChannelSymmetry.simple 0) ↔
          act f (AxisHop.epsAxis 1) = AxisHop.epsAxis 1) := by
    rw [stabilizer_axis_eq]
    decide +kernel
  intro f hd hp
  exact h f (mem_filter.mpr ⟨mem_univ _, hd, hp⟩)

/-- With the same fixed probe as the line, the axis geometry further
restricts the covariance on the original trial encoding. -/
theorem fixed_probe_orders :
    ((stabilizer .axis).filter fun f => act f (AxisHop.epsAxis 1) = AxisHop.epsAxis 1).card = 4 ∧
    ((stabilizer .slice).filter fun f => act f (AxisHop.epsAxis 1) = AxisHop.epsAxis 1).card = 1 := by
  rw [stabilizer_axis_eq, stabilizer_slice_eq]
  decide +kernel

theorem axis_fixed_probe_iff (f : Frame) (h : f ∈ stabilizer .axis) :
    (act f (PMSubstrate.ChannelSymmetry.simple 0) = PMSubstrate.ChannelSymmetry.simple 0 ∨
      act f (PMSubstrate.ChannelSymmetry.simple 0) = -PMSubstrate.ChannelSymmetry.simple 0) ↔
        act f (AxisHop.epsAxis 1) = AxisHop.epsAxis 1 :=
  probe_fix_pair f (mem_filter.mp h).2.1 (mem_filter.mp h).2.2

/-- Fixing the slice without marking a positive clock normal admits
normal reversal. The separate scalar phase is unchanged. -/
def slicePlane : Finset Frame :=
  (stabilizer .axis).filter fun f => act f (AxisHop.epsAxis 3) = AxisHop.epsAxis 3 ∨
    act f (AxisHop.epsAxis 3) = -AxisHop.epsAxis 3

theorem slice_plane_order : slicePlane.card = 8 := by
  rw [slicePlane, stabilizer_axis_eq]
  decide +kernel

theorem slice_plane_generators :
    products (([[1], [2, 3]] : List (List (Fin 4))).toFinset.image wordFrame) 5 =
      slicePlane := by
  rw [slicePlane, stabilizer_axis_eq]
  decide +kernel

theorem fixed_probe_generators :
    products (([[2], [3]] : List (List (Fin 4))).toFinset.image wordFrame) 2 =
      (stabilizer .axis).filter (fun f => act f (AxisHop.epsAxis 1) = AxisHop.epsAxis 1) ∧
    (stabilizer .slice).filter (fun f => act f (AxisHop.epsAxis 1) = AxisHop.epsAxis 1) =
      {identity} := by
  rw [stabilizer_axis_eq, stabilizer_slice_eq]
  decide +kernel

theorem slice_plane_probe_order :
    (slicePlane.filter fun f => act f (AxisHop.epsAxis 1) = AxisHop.epsAxis 1).card = 2 := by
  rw [slicePlane, stabilizer_axis_eq]
  decide +kernel

theorem slice_plane_probe_generators :
    products (([[2, 3]] : List (List (Fin 4))).toFinset.image wordFrame) 1 =
      slicePlane.filter (fun f => act f (AxisHop.epsAxis 1) = AxisHop.epsAxis 1) := by
  rw [slicePlane, stabilizer_axis_eq]
  decide +kernel

/-- A bare line direction has more symmetries than the marked
sector model. This norm-two E8 reflection fixes the positive line
and sends an inactive-sector root out of its orthogonal sector. -/
theorem bare_line_mixing_root :
    let r : SubstrateWeylRoots.Lattice := Pi.single 0 1
    let pairing := PMSubstrate.Lattices.pairing
    let line := SubstrateWeylRoots.root false 0 + 2 • SubstrateWeylRoots.root false 1 +
      SubstrateWeylRoots.root false 2 + SubstrateWeylRoots.root false 3
    let inactive := SubstrateWeylRoots.root true 2
    let active := SubstrateWeylRoots.root false 0
    SubstrateWeylRoots.sector false ![1, 2, 1, 1, 0, 0, 0, 0] = AxisHop.vec OpenHandoff.direction ∧
      pairing r r = 2 ∧ line - pairing line r • r = line ∧ pairing inactive active = 0 ∧
      pairing (inactive - pairing inactive r • r) active ≠ 0 := by
  decide +kernel

/-! ### Bare root line

Use the integral simple-root coordinates of the E8 Gram matrix.
The marked positive edge is the second basis root. Conjugating the
standard highest-root stabilizer gives the seven reflections below.
-/

open PMSubstrate.Lattices

def coordinateRoot (i : Fin 8) : SubstrateWeylRoots.Lattice := Pi.single i 1

def highestRoot : SubstrateWeylRoots.Lattice := ![2, 3, 4, 6, 5, 4, 3, 2]

def toHighest : List (Fin 8) :=
  [3, 2, 0, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7]

def runRootWord (word : List (Fin 8)) (z : SubstrateWeylRoots.Lattice) :
    SubstrateWeylRoots.Lattice :=
  word.foldl (fun x i => SubstrateWeylRoots.reflectIn (coordinateRoot i) x) z

def bareGenerators : Fin 7 → SubstrateWeylRoots.Lattice :=
  ![coordinateRoot 7, coordinateRoot 4, coordinateRoot 6, coordinateRoot 5,
    ![0, 1, 1, 2, 1, 0, 0, 0], coordinateRoot 0, coordinateRoot 2]

theorem bare_line_coordinates :
    coordinateRoot 1 = SubstrateWeylRoots.root false 0 + 2 • SubstrateWeylRoots.root false 1 +
      SubstrateWeylRoots.root false 2 + SubstrateWeylRoots.root false 3 := by
  decide +kernel

theorem bare_conjugating_word :
    runRootWord toHighest (coordinateRoot 1) = highestRoot ∧
      (∀ i : Fin 7, pairing highestRoot (coordinateRoot i.castSucc) = 0 ∧
        runRootWord toHighest.reverse (coordinateRoot i.castSucc) = bareGenerators i) ∧
      pairing highestRoot (coordinateRoot 7) = 1 := by
  decide +kernel

theorem bare_generators_gram :
    (∀ i, pairing (bareGenerators i) (coordinateRoot 1) = 0) ∧
      ∀ i j, pairing (bareGenerators i) (bareGenerators j) = gram i.castSucc j.castSucc := by
  decide +kernel

theorem bare_generators_fix_direction (i : Fin 7) :
    SubstrateWeylRoots.reflectIn (bareGenerators i) (coordinateRoot 1) = coordinateRoot 1 := by
  fin_cases i <;> decide +kernel

theorem bare_reverse_direction :
    SubstrateWeylRoots.reflectIn (coordinateRoot 1) (coordinateRoot 1) = -coordinateRoot 1 := by
  decide +kernel

/-- Sector action on the actual spanning roots. The coefficient
table is computed in the integral substrate Gram matrix. -/
def bareSectorCoefficients (i : Fin 7) (sector : Bool) (j : Fin 4) : ℤ :=
  pairing (SubstrateWeylRoots.root sector j) (bareGenerators i)

theorem bare_generator_sector_action (i : Fin 7) (sector : Bool) (j : Fin 4) :
    SubstrateWeylRoots.reflectIn (bareGenerators i) (SubstrateWeylRoots.root sector j) =
      SubstrateWeylRoots.root sector j - bareSectorCoefficients i sector j • bareGenerators i := rfl

theorem bare_sector_coefficients :
    ∀ i : Fin 7,
      (fun j => bareSectorCoefficients i false j) =
        (![![0,0,0,0], ![0,1,-2,0], ![0,0,0,0], ![0,0,1,-1], ![0,-1,0,2], ![1,0,0,-1], ![-2,1,0,0]] : Fin 7 → Fin 4 → ℤ) i ∧
      (fun j => bareSectorCoefficients i true j) =
        (![![1,-2,1,1], ![0,0,0,0], ![-2,1,0,0], ![1,0,0,0], ![0,0,0,0], ![0,0,-1,0], ![0,0,0,0]] : Fin 7 → Fin 4 → ℤ) i := by
  decide +kernel

end NodeSymmetry

/-! ## Equivariance of factorwise actions -/

set_option maxRecDepth 16000 in
theorem line_probe_equivariant :
    ∀ f, NodeSymmetry.d4 f → NodeSymmetry.preserves .line f →
      Function.Commute (NodeSymmetry.act f) (NodeSymmetry.act (NodeSymmetry.simpleFrame 0)) := by
  have h : ∀ f, NodeSymmetry.d4 f → NodeSymmetry.preserves .line f →
      NodeSymmetry.comp f (NodeSymmetry.simpleFrame 0) =
        NodeSymmetry.comp (NodeSymmetry.simpleFrame 0) f := by
    decide +kernel
  intro f hf hl v
  rw [← NodeSymmetry.act_comp, h f hf hl, NodeSymmetry.act_comp]

theorem slice_probe_not_equivariant :
    ¬ Function.Commute (NodeSymmetry.act (NodeSymmetry.simpleFrame 1))
      (NodeSymmetry.act (NodeSymmetry.simpleFrame 0)) := by
  intro h
  have hn : NodeSymmetry.act (NodeSymmetry.simpleFrame 1)
      (NodeSymmetry.act (NodeSymmetry.simpleFrame 0) (AxisHop.epsAxis 0)) ≠
      NodeSymmetry.act (NodeSymmetry.simpleFrame 0)
      (NodeSymmetry.act (NodeSymmetry.simpleFrame 1) (AxisHop.epsAxis 0)) := by
    decide +kernel
  exact hn (h (AxisHop.epsAxis 0))

/-- Apply the same channel matrix in every live and record cell. -/
def bankAction {R : ℕ} (A : PacketGaugeActions.M) (bank : PacketBank R) : PacketBank R :=
  fun p => (A *ᵥ (fun a => bank (p.1, a))) p.2

theorem fifo_commutes_bankAction (R : ℕ) (A : PacketGaugeActions.M) :
    Function.Commute (fifoEquiv R) (bankAction A) := by
  intro bank
  rfl

/-- For a factorwise relabelling, equivariance requires the corresponding
core commutation and one covariance equation on the bank fibre. -/
theorem joint_commutes_iff {I : Type*} {R : ℕ} (core : I → I)
    (packet : I → Equiv.Perm (PacketBank R)) (renameCore : I → I)
    (renameBank : PacketBank R → PacketBank R) :
    Function.Commute (jointTick core packet) (Prod.map renameCore renameBank) ↔
      Function.Commute core renameCore ∧
        ∀ i bank, packet (renameCore i) (renameBank bank) =
          renameBank (packet i bank) := by
  constructor
  · intro h
    exact ⟨fun i => congrArg Prod.fst (h (i, 0)),
      fun i bank => congrArg Prod.snd (h (i, bank))⟩
  · rintro ⟨hc, hp⟩ s
    exact Prod.ext (hc s.1) (hp s.1 s.2)

/-- Idle and FIFO commute with every cellwise channel matrix as soon as
the core relabelling itself commutes. This includes all certified packet
gauge matrices, even without using their unitarity. -/
theorem hold_fifo_equivariant {I : Type*} (R : ℕ) (core renameCore : I → I)
    (hc : Function.Commute core renameCore) (A : PacketGaugeActions.M) :
    Function.Commute (jointTick core (fun _ => Equiv.refl (PacketBank R)))
      (Prod.map renameCore (bankAction A)) ∧
    Function.Commute (jointTick core (fun _ => fifoEquiv R))
      (Prod.map renameCore (bankAction A)) :=
  ⟨(joint_commutes_iff _ _ _ _).2 ⟨hc, fun _ _ => rfl⟩,
    (joint_commutes_iff _ _ _ _).2 ⟨hc, fun _ => fifo_commutes_bankAction R A⟩⟩

/-! ## Conserved totals -/

theorem ring_stream_total {n : ℕ} (either : Bool) (s : RingReceiver.State n)
    {M : Type*} [AddCommMonoid M] (measure : Bool → M) :
    (∑ x, (measure ((RingReceiver.tick n either s).2.2.2 x).1 +
      measure ((RingReceiver.tick n either s).2.2.2 x).2)) =
      ∑ x, (measure (s.2.2.2 x).1 + measure (s.2.2.2 x).2) := by
  calc
    _ = ∑ x : Fin n, (measure (s.2.2.2 ((finRotate n).symm x)).1 +
        measure (s.2.2.2 (finRotate n x)).2) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [RingReceiver.tick_ports]
      change (measure (LocalController.applyGuard
        (fun _ => RingReceiver.exchange either (s.2.1 x))
        ((s.2.2.2 ((finRotate n).symm x)).1, (s.2.2.2 (finRotate n x)).2)).1 + _) = _
      cases h : RingReceiver.exchange either (s.2.1 x) <;>
        simp [LocalController.applyGuard, RingReceiver.arrivals, OpenReferenceFlow.streamShift,
          add_comm]
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [Equiv.sum_comp (finRotate n).symm (fun x => measure (s.2.2.2 x).1),
        Equiv.sum_comp (finRotate n) (fun x => measure (s.2.2.2 x).2)]

/-- Every fixed per-channel total across the bank is preserved. For
population take `measure = Complex.normSq`. No per-cell assertion follows. -/
theorem fifo_channel_total (R : ℕ) (bank : PacketBank R) (a : PacketGaugeActions.Channels)
    {M : Type*} [AddCommMonoid M] (measure : ℂ → M) :
    (∑ i : Fin (R + 1), measure (fifoEquiv R bank (i, a))) =
      ∑ i : Fin (R + 1), measure (bank (i, a)) :=
  Equiv.sum_comp (finRotate (R + 1)) (fun i => measure (bank (i, a)))

/-- An algebraic counterexample to the implication from invertibility
and channel equivariance to conservation of population. -/
private noncomputable def doubleBank (R : ℕ) : Equiv.Perm (PacketBank R) where
  toFun f p := 2 * f p
  invFun f p := f p / 2
  left_inv f := by funext p; dsimp; ring
  right_inv f := by funext p; dsimp; ring

theorem equivariant_lift_can_change_population (a : PacketGaugeActions.Channels) :
    ∃ e : Equiv.Perm (PacketBank 0),
      (∀ A : PacketGaugeActions.M, Function.Commute e (bankAction A)) ∧
      (∑ i : Fin 1, Complex.normSq (e (fun _ => 1) (i, a))) ≠
        ∑ _i : Fin 1, Complex.normSq (1 : ℂ) := by
  refine ⟨doubleBank 0, ?_, ?_⟩
  · intro A bank
    funext p
    change 2 * (∑ i, A p.2 i * bank (p.1, i)) =
      ∑ i, A p.2 i * (2 * bank (p.1, i))
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => mul_left_comm 2 (A p.2 i) (bank (p.1, i)))
  · norm_num [doubleBank, Complex.normSq_apply]

/-! ## A clock phase is not selected by the excursion account -/

theorem shifted_excursion_boundaries :
    CarrierReferenceCycle.boundaries (fun t => decide (t = (2 : Fin PMSubstrate.E8Values.Delta))) = {1, 2} := by
  decide +kernel

theorem shifted_excursion_same_cost (c : Fin 3) (toll : ℝ) :
    PMSubstrate.NetCost.expectedCost toll
        (CarrierReferenceCycle.carrierEvents c (fun t => decide (t = (2 : Fin PMSubstrate.E8Values.Delta)))) =
      PMSubstrate.NetCost.expectedCost toll
        (CarrierReferenceCycle.carrierEvents c CarrierReferenceCycle.excursionMask) := by
  rw [CarrierReferenceCycle.carrier_cost_for_mask, shifted_excursion_boundaries,
    CarrierReferenceCycle.carrier_cycle_cost]
  norm_num

end PMKAutomaton.Components
