# Transport premise ledger

This is the status ledger for [REVIEW-AND-NEXT](REVIEW-AND-NEXT.md).
Derived and excluded results retain the hypotheses of their theorems.
The [clock ledger](CLOCK.md) records timing and the
[writer schedule](../PMElementaryParticles/SCHEDULE.md) records costs.

## Admission

Admission is the root premise. A candidate trace specifies its occupied
inputs, the port that feeds each operation, the guard that fires it, and
the output and retained record. A physical admission law must authorize
those operations together on the stated input and reference states.

**Smallest question.** For each candidate operation, which occupied port
feeds it and which guard fires it while the required record stays
available? Give an executable answer for the live state and its record
together.

| Open part of Admission | What it decides | Smallest question |
| --- | --- | --- |
| Spatial and receiver update | Whether the root hop, wall loader and spatial shift run, and whether the receiver exchanges or bypasses. | Which occupied port and retained branch enable each native operation? |
| Heavy writer and sampling | Which live sequence feeds the direct heavy writer. This fixes the booked population or required-read set and the treatment of the vacancy. | Which port feeds the writer, and on which of its arrivals does the guard fire? |
| Heavy branch and record reference | Whether either electric writer and the guarded companion crossing are admitted. With paid output flags and separate balanced per-bit resets, the colour advantage bounds the remaining cost at 3/4, 27/32 or 9/10 per input for full-probe, idle-vacancy or occupied-only uniform sampling. | What jointly admits the supplied seed, polarity, record write and the guarded use on both walls? Which output record is retained? |
| Lightest-offset branch | Whether the retained matched plus branch and static vector-class test can drive the charged offset. Its firing law also affects PMFlavor's in-cycle wall record. | Can the joint selector fire the static insertion using an occupied, retained record and preserve the required calibration? |
| Label-sensitive and successive handoffs | Which crossings occur for a retained label and whether successive through probabilities multiply. | What is the through law conditional on the preceding history and its record? |
| Trial histories and phase controls | Whether the physical controller realizes the four retained two-request histories, with equal prior counts for the Gibbs calculation. A principal-range calibration is another conditional route. | Can the controller produce and retain each of the four histories with equal prior counts, or certify that the accumulated phase lies in the principal range? |
| Joint schedule and Hamiltonian update | Which visits, overlaps and controls the two walls can execute. With timing and coefficient readout this decides the physical schedule, the ratio `r`, and the split walk with or without the lazy offset. | Which admitted chronological word acts on the wire and record together, including the controlled crossings, wall insertions, and any one-wall offset? |
| Shared-register event ownership | Which charged-current and writer records each persisting label needs, and which are retained, reused or exported. This extends the single-event requirement table. | Which labels are present at each visit and which subsequent guard consumes each record? |

The [conditional reset thresholds](../PMElementaryParticles/SCHEDULE.md#record-reference-remains-undetermined)
also require the Registration tariff and Sustained reference supply.
They are tests of admitted candidates.

## Absolute timing

**Decision.** This premise fixes elapsed tick counts, available
windows, the cadence on both walls and the physical wall rates. With
Admission and the pulse-area and coefficient normalization it fixes
`r = K_f/|y|` and the inputs to `LightLeakage` and `WallGapCalibration`.

**Smallest question.** How many substrate ticks does each admitted
operation occupy, and what phase area and Hamiltonian coefficient
does that operation realize on the stated slots? Supply either the
statistical-pair calibration on the coherent clock or a calibrated
principal-range pulse.

**Dependence.** Admission supplies the operation and the allowed
concurrency. The clock period and conditional word bounds hold
before this identification.

## Registration tariff

**Decision.** This premise converts the comparison flags and the
unmatched preparation, polarity-control, export, reset, renewal and
maintenance jobs into paid registrations. It decides the signed
remainder in the reference comparison and the Toll for each label.

**Smallest question.** For the admitted traces in common units, which
visits register and what is the difference in paid work after matching
the same jobs at their required state and time?

**Dependence.** Admission determines the visits, participating labels
and continuing branch. A registration is already priced in units of one
expected flagged outcome. The assignment of physical visits and prices
beyond that flag account remains open.

## Sustained reference supply

**Decision.** This premise decides the occupation and lifetime of the
reference and record train. It also decides whether either writer can
use maintenance already performed by a refresh.

**Smallest question.** Which occupied odd seed and axis supplies the
required reference at each admitted visit, and where does its displaced
record go when the reference is renewed?

**Dependence.** The supply and open-orbit theorems hold for supplied
states and routing. Which states, resets and renewal times are needed
depends on Admission. The bookkeeping for baseline weak and
hypercharge reference sharing alone leaves the writer's reuse open.

## Disturbance and acceptance

**Decision.** This premise gives the viability margin of a sustained
handoff under the stated disturbance.

**Smallest question.** Which incoming reference errors may the
receiver accept at its admitted visits?

**Dependence.** The acceptance equivalence is independent of Admission.
Its physical tolerance and incoming disturbance must be attached to
the admitted operation and supplied orbit.

## Layering

**Decision.** This is a build-boundary choice. PMAction and
`PMTransport.Machine` share finite dependencies. The packet interface
sits above PMConstants. See [the working premise](PREMISE.md#layering)
and the [dependency audit](../AuditDependencies.lean).

**Smallest question.** If a stand-alone machine build is needed, which
common finite base will the two layers import, with the existing
module paths preserved? The current boundary includes
`StateIdentification`, `CommonResponse`, `ChiralityConvention`,
`InvolutionComparison`, `RestorationResponse`, `SelectedSampling`,
`SubstrateReflection` and `GaugeRecordEmbedding`.

**Dependence.** This choice is independent of physical Admission.
It remains parked.

## Checked boundaries

| Status | Item | Certificate and scope |
| --- | --- | --- |
| Derived | Two-site arrivals, destinations and comparison flags | `TwoSiteHandoff.step_trace`, `export_trace`, `receiver_agrees_with_line`, `hop_flag`, `exchange_flag`. These describe the supplied spatial and exchange operations. |
| Derived | Open route geometry and supply | `OpenHandoff.address_is_site`, `address_step`, `receiver_trace`, `export_trace`, `sum_exported` give the root line, both arrivals and export population. `acceptance_iff_supply` and `population_required` characterize the upstream reference needed over a finite horizon. `RecordSupply.lattice_forever` gives repeat restoration for an already supplied open orbit. |
| Derived | Unit seed loading and the odd candidate | `OpenHandoff.basis_loading_iff` specifies the old occupied input. `OddReferenceSource.rest_stationary`, `load_rest_mode`, `loading_pulse_stays_at_rest`, `odd_seed_train_restores` give the odd substitute, its loader and the required unit population per visit. |
| Excluded | Preparing the old sharp basis seed from odd input by the checked phases | `OddReferenceSource.root_phase_word_no_basis`. |
| Excluded | Indefinite clean reuse by the closed exchange alone | `TwoSiteHandoff.exchange_four_returns` closes the trajectory. `four_restorations_iff` requires every slot to start at the reference. `RecordSupply.ring_returns` returns the disturbance on a finite orbit. |
| Excluded | Inferring writer traffic from ready-reference supply | `OpenHandoff.any_incoming_trace` restores the same reference for every supplied incoming live sequence. |
| Derived | Two-stream through weight and the independent direct path | `HandoffAdmittance.through_eq_conductance` and `handoff_from_conductance` give the through weight for the stipulated current model. `direct_crossing` and `direct_crossing_prob` identify the all-pass history and price its probability for independent equal through weights. |
| Derived | Period, word length and common-tick formula | `E8Values.Delta_eq`, `CarrierReferenceCycle.excursion_boundaries`, `ClassBlindFlip.forwardTimes_total`, `SplitClassBlindFlip.duration_eq`, `RootTransferPhase.half_pulse_word`, `CertainTransferRate.common_tick_rate_ratio`. The rate ratio still uses the two areas and coefficient conversions. |
| Excluded | Single-frame execution of the stated long serial word | `ClassBlindFlip.certain_does_not_fit_e8_frame` and `certain_with_six_reflections_lower` exclude it at whole-tick certain transfer. `SplitClassBlindFlip.one_tick_budget` gives a different conditional elapsed budget for a short word and one crossing. |
| Excluded | Selecting the coherent gap from whole-tick samples alone | `RootClockCalibration.phase_alias_iff`, `integer_samples_agree` and `ambiguous_exchange_clock`. A principal-range witness or an admitted statistical probe is needed. |
| Derived | Two trial slots, endpoint law and time conversion | `ClockedRootTrials.ticks_zero_one`, `ticks_one_two`, `shared_request_returns`, `matches_independent_trial_weight` give separate requests and the `p²` criterion. `RootClockCalibration.gap_from_trials` and `trial_weight_inj` give identification from the admitted statistic. `ClockedRootTrials.heat_after_two_ticks` and `phase_in_ticks` give the two-tick conversion under the stated identification. |
| Excluded | Common chiral anticommutation with the specified one-wall offset | `NativeWallOffset.rest_offset_breaks_chirality`. |
| Derived | Companion seed, setup and current traces | `ElectricChiralKick.clean_first_seed_at_rest`, `two_kicks_from_one_current`, `swapped_exposure_toll`, `total_tolls`; `ElectricCompanionBank.prepares_companion_bank`, `guarded_companion_transport`; `ElectricCompanionSetupToll.short_setup_on_seed_support`, `primitive_setup_sum`. These use a supplied occupied seed and give conditional flag or root counts. |
| Excluded | Fresh inverse-decoder and decoder within one serial frame | `ElectricCoordinateDecoder.fresh_bank_serial_exceeds_clock` at at least one tick per quarter-time. |
| Excluded | Bare untagged heavy selection or closed universal cleaning | `HeavyFlipControl.no_root_only_direct_address` and `HeavyFlipNativeBoundary.no_closed_cleaning`. `ElectricCompanionBank.written_port_ready_iff` restricts reuse via companion advance to the active neutral port. |
| Derived | Record transport and the conditional reset flag | `OpenHandoff.sum_exported` preserves the exported population. `CoherentRecordRestoration.prepared_repair`, `unitary_reset_factorization` retain the displaced distinction. `OpenHandoff.balanced_basis_repair_flag` gives a half flag for a balanced written one against fresh zero in the admitted basis circuit. `twice_undoes` excludes silent reuse of the occupied record. |
| Derived | Single-event record requirements | `EventRequirements.pairs_of_sign`, `axis_cannot_choose`, `full_reads_both` give the charged-current doublet requirement. `RefreshMap.asymmetric_gate_records` and `CoherentGate.unequal_needs_orthogonal` constrain the records. |

## Next derivation

An admitted trace gives the occupied live, reference and record ports at
each tick, the guard and request at each operation, and the next state of
all those ports, including idle alternatives and displaced records.

`ClockedRootTrials` supplies the two retained slots and the joint-weight
test for independent trials. An equal-prior history account requires
equal prior counts of all four retained histories and equal local action
for both changes. `BranchPulseContract.comparison_mem` and
`program_correct` constrain the supplied comparison and control.
`RegisterControl.extend_encode`, `occupation_conserved` and
`phase_unitary` constrain its reversible realization.
`PersistenceSelection.within_family_iff_cheapest` selects from the
resulting family once its costs are supplied.

Derive which occupied ports and native guards generate the trace on
the E8 clock. Show which histories and their prior counts follow,
how the record stays available until consumed or exported, and which
reference is ready at each repeat visit. This should identify the
writer's booked input mass and the admitted heavy and light branches.
For the reference comparison, derive or bound the signed difference
in paid work on that family.
