# Transport premise ledger

This ledger follows [REVIEW-AND-NEXT](REVIEW-AND-NEXT.md). Derived and
excluded entries apply under the cited hypotheses. An open premise
names the input still needed for a physical conclusion. The
[clock ledger](CLOCK.md) gives the timing certificates. The
[writer lifecycle](../PMElementaryParticles/SCHEDULE.md#marginal-cost-of-the-two-references)
gives the price account.

## Node handoff

| Status | Item | Certificate or what the premise would decide |
| --- | --- | --- |
| Derived | Two-site arrivals, destinations and comparison flags | `TwoSiteHandoff.step_trace`, `export_trace`, `receiver_agrees_with_line`, `hop_flag`, `exchange_flag`. These describe the supplied spatial and exchange operations. |
| Derived | Open route geometry and supply | `OpenHandoff.address_is_site`, `address_step`, `receiver_trace`, `export_trace`, `sum_exported` give the root line, both arrivals and export population. `acceptance_iff_supply` and `population_required` characterize the upstream reference needed over a finite horizon. `RecordSupply.lattice_forever` gives repeat restoration for an already supplied open orbit. |
| Derived | Unit seed loading and the odd candidate | `OpenHandoff.basis_loading_iff` specifies the old occupied input. `OddReferenceSource.rest_stationary`, `load_rest_mode`, `loading_pulse_stays_at_rest`, `odd_seed_train_restores` give the odd substitute, its loader and the required unit population per visit. |
| Excluded | Preparing the old sharp basis seed from odd input by the checked phases | `OddReferenceSource.root_phase_word_no_basis`. |
| Excluded | Indefinite clean reuse by the closed exchange alone | `TwoSiteHandoff.exchange_four_returns` closes the trajectory. `four_restorations_iff` requires every slot to start at the reference. `RecordSupply.ring_returns` returns the disturbance on a finite orbit. |
| Excluded | Inferring writer traffic from ready-reference supply | `OpenHandoff.any_incoming_trace` restores the same reference for every supplied incoming live sequence. |
| Named premise | Spatial and receiver admission | Admit the root hop, spatial translation, wall loader and receiver exchange on the actual occupied modes. Identify the physical exchange/bypass trigger. This decides which endpoint trace the node executes. The clock and tariff are separate inputs below. |
| Named premise | Occupied vacuum seed and renewal | Identify the accessible populated odd seed and its axis. Supply the train for the selected horizon or construct a reversible renewal with its record destination. This decides sustainable reference supply. |
| Named premise | Disturbance and acceptance rule | Specify the actual tolerances and disturbance family on the incoming reference train. Apply `acceptance_iff_supply` to determine the viability margin. |
| Derived | Two-stream through weight and the independent direct path | `HandoffAdmittance.through_eq_conductance` and `handoff_from_conductance` give the through weight for the stipulated current model. `direct_crossing` and `direct_crossing_prob` identify the all-pass history and price its probability for independent equal through weights. |
| Named premise | Label-sensitive through law and successor dependence | Derive the comparator and tariff with the label retained. Give the conditional through weights or independence across the actual nodes. This decides whether the through probabilities multiply and which branch feeds a writer. |

## Absolute event clock

| Status | Item | Certificate or what the premise would decide |
| --- | --- | --- |
| Derived | Period, word length and common-tick formula | `E8Values.Delta_eq`, `CarrierReferenceCycle.excursion_boundaries`, `ClassBlindFlip.forwardTimes_total`, `SplitClassBlindFlip.duration_eq`, `RootTransferPhase.half_pulse_word`, `CertainTransferRate.common_tick_rate_ratio`. The rate ratio still uses the two areas and coefficient conversions. |
| Excluded | Single-frame execution of the stated long serial word | `ClassBlindFlip.certain_does_not_fit_e8_frame` and `certain_with_six_reflections_lower` exclude it at whole-tick certain transfer. `SplitClassBlindFlip.one_tick_budget` gives a different conditional elapsed budget for a short word and one crossing. |
| Excluded | Selecting the coherent gap from whole-tick samples alone | `RootClockCalibration.phase_alias_iff`, `integer_samples_agree` and `ambiguous_exchange_clock`. A principal-range witness or an admitted statistical probe is needed. |
| Derived | Two trial slots, endpoint law and time conversion | `ClockedRootTrials.ticks_zero_one`, `ticks_one_two`, `shared_request_returns`, `matches_independent_trial_weight` give separate requests and the `p²` criterion. `RootClockCalibration.gap_from_trials` and `trial_weight_inj` give identification from the admitted statistic. `ClockedRootTrials.heat_after_two_ticks` and `phase_in_ticks` give the two-tick conversion under the stated identification. |
| Named premise | Physical trials and their equal prior counts | Admit the four retained histories, identify the two local registrations and price the local action. The local Gibbs extension `history_mass_factorizes` derives the product law under equal prior counts and local additive action. Alternatively derive a physical first-half-turn bound and calibrate its comparison (`RootClockCalibration.principal_flag_inj`). This decides the gap used by the real controller. |
| Named premise | Shared hop-time unit and control windows | Identify statistical-pair time with the coherent elapsed clock. Admit the generation and chirality controls and the words in `ClassBlindFlip`, `RootCliffordCompletion`, `CompletedCarrierPhase` and `SelectiveCarrierRouting`. Specify allowed phases, serial or parallel use of slots, and cadence on both walls. This decides per-route periods and event durations. |
| Named premise | Pulse areas, physical tariff and coefficient readout | Derive the phase gain and registration account for each fired operation, including node and crossing. Identify its normalization in the wire Hamiltonian. This fixes the absolute rates, `r` and the inputs to `LightLeakage` and `WallGapCalibration`. The first-row diagnostic is [comparison only](../PMFlavor/REVIEW-AND-NEXT.md#first-row-wall-leakage). |
| Excluded | Common chiral anticommutation with the specified one-wall offset | `NativeWallOffset.rest_offset_breaks_chirality`. |
| Named premise | Physical split update and offset | Specify the chronological split update (`SplitClockBoundary`) and whether the lazy offset persists. This decides the operator used for the daughter spectrum and leakage calculation. |

## Label-sensitive handoff

| Status | Item | Certificate or what the premise would decide |
| --- | --- | --- |
| Derived | Companion seed, setup and current traces | `ElectricChiralKick.clean_first_seed_at_rest`, `two_kicks_from_one_current`, `swapped_exposure_toll`, `total_tolls`; `ElectricCompanionBank.prepares_companion_bank`, `guarded_companion_transport`; `ElectricCompanionSetupToll.short_setup_on_seed_support`, `primitive_setup_sum`. These use a supplied occupied seed and give conditional flag or root counts. |
| Excluded | Fresh inverse-decoder and decoder within one serial frame | `ElectricCoordinateDecoder.fresh_bank_serial_exceeds_clock` at at least one tick per quarter-time. |
| Excluded | Bare untagged heavy selection or closed universal cleaning | `HeavyFlipControl.no_root_only_direct_address` and `HeavyFlipNativeBoundary.no_closed_cleaning`. `ElectricCompanionBank.written_port_ready_iff` restricts reuse via companion advance to the active neutral port. |
| Named premise | Joint companion and payload firing | Supply the predecessor-class seed and admit the coupled current, guarded crossing and companion update. Allocate the one- and two-root setups and remaining serial visits in the physical clock windows. This decides where each insertion fires and how often. |
| Derived | Record transport and the conditional reset flag | `OpenHandoff.sum_exported` preserves the exported population. `CoherentRecordRestoration.prepared_repair`, `unitary_reset_factorization` retain the displaced distinction. `OpenHandoff.balanced_basis_repair_flag` gives a half flag for a balanced written one against fresh zero in the admitted basis circuit. `twice_undoes` excludes silent reuse of the occupied record. |
| Named premise | Booked writer population | Identify the stream and port feeding the direct heavy writer, then what its guard admits, including whether the vacancy is visited. Decide sampled expectation versus required reads. `WireReferenceCost.booked_population_difference` gives the bit gap for any common booked population. |
| Named premise | Registration and record lifecycle | Select the physical comparator, retained branch and paid flags. Match preparation, export, reset, renewal and maintenance jobs across references at their required state and time. This decides the remaining signed cost difference for the [polarity threshold](../PMElementaryParticles/SCHEDULE.md#record-reference-remains-undetermined). `HandoffAdmittance.closure_one_price` applies only under its relabeling premise. |
| Derived | Single-event record requirements | `EventRequirements.pairs_of_sign`, `axis_cannot_choose`, `full_reads_both` give the charged-current doublet requirement. `RefreshMap.asymmetric_gate_records` and `CoherentGate.unequal_needs_orthogonal` constrain the records. |
| Named premise | Shared-register event ownership | Determine which inputs participate in each comparison and which records must be retained, reused or exported for each persisting label. This extends the single-event table to per-label Toll. It decides the heavy weight, lightest-offset firing law and PMFlavor's in-cycle wall record. |

## Machine dependencies

| Status | Item | Certificate or what the premise would decide |
| --- | --- | --- |
| Named premise | Stand-alone build boundary | A separate machine target would need a common finite dynamics base across the current PMAction and machine dependencies. The boundary modules are listed in [REVIEW-AND-NEXT](REVIEW-AND-NEXT.md#machine-dependencies). The [layering decision](PREMISE.md#layering) remains parked. |
