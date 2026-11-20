import PMKAutomaton.TwoSiteHandoff
import PMKAutomaton.OpenHandoff
import PMKAutomaton.OddReferenceSource
import PMKAutomaton.HandoffAdmittance
import PMKAutomaton.ClockedRootTrials
import PMKAutomaton.Machine.CoherentGate
import PMKAutomaton.Machine.CoherentRecordRestoration
import PMKAutomaton.Machine.CoherentRefresh
import PMKAutomaton.Machine.RecordSupply
import PMKAutomaton.Machine.RegisterControl
import PMKAutomaton.Machine.GluedRegister
import PMKAutomaton.Machine.ReferenceClassHop
import PMKAutomaton.Machine.SubstrateWeylRoots
import PMKAutomaton.Machine.RecordTransport
import PMKAutomaton.Machine.RegisterInteraction
import PMKAutomaton.Machine.CarrierTriality
import PMKAutomaton.Machine.ClockControlledRoot
import PMKAutomaton.Machine.RootBranchEncoding
import PMKAutomaton.Machine.InBandRootReadout
import PMKAutomaton.Machine.CarrierWeyl
import PMAction.TollAmplitude
import PMAction.DiagonalReadout
import PMAction.PersistenceSelection
import PMAction.SplitClassBlindFlip
import PMAction.CertainTransferRate
import PMAction.GenerationOrientation
import PMAction.ReferenceNode

/-!
# Public transport interface

The exports keep the hypotheses and conclusions of the source theorems.
The original namespaces remain available for existing callers. Premise
names refer to `PMKAutomaton/PREMISES.md`. The physical update is a
client obligation. Phase, branch, reader and work choices appear in
the original hypotheses. The closure ledger is in `COMPONENTS.md`.

## Protocol inputs supplied by EP

KAutomaton's open list contains machine inputs only. The following are
protocol inputs owned by EP, not KAutomaton:

* the retained request field and firing pattern G (`firingPattern`,
  `bitRingTotal43_eq`);
* the excitation occupancy and reference-record choice O (`refRecord`,
  `bitRingEmbed`, `bitToll_eq_hamming`);
* the label record, reference and comparison angle theta in the EP half of U;
  the certified phase set is `{0, π}` (`PhaseToRecord`);
* which label record W reads;
* the label Toll and paid-event choice in the EP half of K;
* the history/prior family H.

EP supplies these from persistence; KAutomaton only supplies the machine
comparator, receiver-flag computation, tariff unit, links, boundary, clock and
job mechanics. The six individual pillar predicates are not defined in
`PersistenceMechanics.Requirements`; expressing them on `Protocol` is an EP
open definition, not a KAutomaton input.
-/

namespace PMKAutomaton.Interface

/-! ## Handoff

Admission supplies the occupied ports, spatial shift and exchange or
bypass guard. Absolute timing supplies the physical pulse calibration.
The conductance result uses the two-stream current law. A product of
through weights also needs the successor-dependence part of Admission.
-/

namespace Handoff

export PMKAutomaton.TwoSiteHandoff (State step port_count step_trace receiver_agrees_with_line
  first_reference_iff second_reference_iff exchange_four_returns four_restorations_iff
  native_step_observed hop_flag exchange_flag receiver_half_pulse)

export PMAction.OpenReferenceFlow (exchange_reflects bypass_transmits)

export PMConstants.HandoffAdmittance (receiver_exchange_or_bypass repair_receiver_after_exchange
  leftOutflow node_current through_eq_conductance handoff_from_conductance
  transmission_of_linear handoff_is_alpha pulse_calibration_transfers direct_crossing
  direct_crossing_prob closure_one_price)

/-- Specialize the conductance identity to the through weight of a pulse
of angle `t`. The hypothesis supplies the conductance in open-channel units. -/
theorem through_weight_eq_alpha (t : ℝ)
    (h : ∀ nL nR, leftOutflow (Real.cos t ^ 2) nL nR - nL =
      PMSubstrate.causalCoupling * (nR - nL)) :
    Real.cos t ^ 2 = PMSubstrate.causalCoupling :=
  through_eq_conductance h

end Handoff

/-! ## Record

Admission supplies the encoded register, retained output and route.
Sustained reference supply provides the ready state at each visit.
Disturbance and acceptance supplies the tolerance when restoration is
approximate. Registration tariff applies only when a comparison is paid.
-/

namespace Record

export PMElementaryParticles.CoherentGate (recorded_orthogonal_iff unequal_needs_orthogonal)
export PMKAutomaton.OpenHandoff (receiver_trace export_trace any_incoming_trace sum_exported
  acceptance_iff_supply population_required basis_population_required basis_loading_iff
  receiver_flag balanced_basis_repair_flag neighbours_do_not_determine_second_visit)
export PMKAutomaton.OddReferenceSource (rest_stationary rest_population load_rest_mode
  loading_pulse_stays_at_rest odd_seed_train_restores)
export PMAction.RecordTransport (tick_fifo tick_norm stream_conserved)
export PMAction.RecordSupply (run live_at_site clean_supply disturbance_exported
  open_orbit_forever lattice_forever ring_returns)
export PMAction.CoherentRecordRestoration (prepared_repair twice_undoes
  unitary_reset_factorization)
export PMAction.RegisterControl (extend extend_encode occupation_conserved phase_unitary)
export PMAction.BranchPulseContract (program_correct comparison_mem)

end Record

/-! ## Cost

Admission supplies the included visits, their inputs and the continuing
branch. Registration tariff identifies which flags register and what
additional work is paid. The wire amplitude is for the unflagged
survival account. Persistence compares a supplied family and cost.
-/

namespace Cost

export PMSubstrate.NetCost (prob expectedCost expected_count_linear)
export PMAction.DiagonalReadout (flag flag_bounds transport_eq_diagonal transport_flag state_flag)
export PMAction.TollAmplitude (scheduleToll rare_registration_limit unflagged_scale wireWeight
  wireAmplitude wireAmplitude_eq wireAmplitude_sq wireAmplitude_lt_iff amplitude_ratio
  ratio_ge_iff schedule_factorizes)
export PMAction.PersistenceSelection (most_persistent_iff_cheapest within_family_iff_cheapest
  survival_strictAnti event_price_pos)
export PMAction.RefreshSchedule (cost admissible minimal_attained minimal_is_ledger strict_if_extra)
export PMAction.CoherentRefresh (Restores minimum_cost minimum_once)

end Cost

/-! ## Clock

The 43-phase period is the substrate period. Admission supplies the
pulse words and permits their use on occupied registers. Absolute timing
identifies their elapsed time on the physical clock. Integral certain
flip bounds apply to the specified serial words. The trial histories
retain their initial requests through the period. Their prior counts
require Background occupancy and boundary supply.
-/

namespace Clock

export PMAction (Delta Delta_eq)
export PMAction.RootTransferPhase (gap quarterTime quarter_pulse half_pulse half_pulse_word)
export PMAction.CarrierReferenceCycle (clock_visits clock_closes excursion_boundaries
  carrier_cost_for_mask minimum_nonidle_carrier_cost)
export PMAction.ClockControlledRoot (cycle_closes)
export PMAction.ClassBlindFlip (forwardTimes_total certain_quarter_even
  certain_tick_duration_lower certain_tick_duration_attained certain_does_not_fit_e8_frame
  certain_with_six_reflections_lower)
export PMAction.SplitClassBlindFlip (duration_eq pulse_completed one_tick_budget)
export PMKAutomaton.RootClockCalibration (phase_alias_iff integer_samples_agree trial_weight
  gap_from_trials trial_weight_inj principal_flag_inj)
export PMKAutomaton.ClockedRootTrials (ticks_zero_one ticks_one_two shared_request_returns
  iterate_controls quiet_trial_tick trial_period_endpoint historyCount history_count_pos_iff
  all_pairs_history_count shared_request_history_count history_mass_factorizes
  matches_independent_trial_weight heat_after_two_ticks phase_in_ticks)
export PMAction.CertainTransferRate (certain_min common_tick_rate_ratio)

end Clock

/-! ## Route

The glue address fixes the two classes with a frozen wall orientation.
The reference-class test is relative to the chosen stationary reference.
Admission supplies the physical insertions and crossings. The node
series result uses two equal restoring legs.
-/

namespace Route

export PMAction.GenerationWalls (side omitted encode decode_side side_decode one_class_per_wall
  balanced_classification exchange_not_generation_only)
export PMAction.GenerationOrientation (side_classes type_is_gen type_label swap_keeps_label)
export PMAction.ReferenceClassHop (stationary_iff out_of_reference_kills_light
  touches_reference_class)
export PMAction.ReferenceNode (restoring_two_classes direct_three_classes restoring_series)
export PMElementaryParticles.GluedRegister (crossing_walls crossing_word_glued crossing_word_pure)

end Route

/-! ## Symmetry

These identities apply to the embedded simple roots. Link admission
and carrier realization supply the markings and the action on a
physical node. The root laws do not select an equivariant lift.
-/

namespace Symmetry

export PMAction.CarrierWeyl (simple_is_root)
export PMAction.SubstrateWeylRoots (embedding_intertwines sector_intertwines
  preserves_norm preserves_glue)

end Symmetry

/-! ## Wire operations

These are the finite carrier, bank and readout operations used by EP.
The statements retain admission, timing and preparation conditions.
-/

namespace Wire

namespace Carrier
export PMAction.CarrierWeyl (lookup lookup_antipode)
export PMKAutomaton.CarrierTriality (carrierTriality carrierTriality_vector carrier_is_glued
  diagonalRoot glued_triality_step trialityMatrix triality_cube triality_observed triality_unitary)
end Carrier

namespace Glued
export PMElementaryParticles.GluedRegister (M Wt bit carrier crossing dot neg_class neg_ne
  refl reflectPair root runCrossing triality wallStep_class)
end Glued

namespace RootBranch
export PMAction.RootBranchEncoding (embed population root_action swap)
end RootBranch

namespace Registers
export PMAction.RegisterInteraction (current current_observed current_unitary evolution_occupation)
end Registers

namespace Probe
export PMAction.InBandRootReadout (events record schedule_closes scheduled_read)
export PMAction.ClockControlledRoot (State fire update)
end Probe

end Wire

end PMKAutomaton.Interface
