# Clock and firing schedule

## Certified clock results

Here `Q = RootTransferPhase.quarterTime p`. The parameter `p` is a root
attempt rate. A certificate in this table holds under the hypotheses in
its theorem.

| Status | Result | Certificate and scope |
| --- | --- | --- |
| Certified | The substrate has 43 phases. The reference can follow a closed excursion with two boundaries, at phases 0 and 1. The idle mask also closes. | `PMSubstrate.E8Values.Delta_eq`, `CarrierReferenceCycle.clock_visits`, `cycle_closes`, `excursion_boundaries`, `idle_cycle_cost`. A moving carrier changes at both excursion boundaries. |
| Certified | In statistical-pair time, `Q = π/(2 gap(p))`, where `gap(p) = −2 log(1−2p)`. The principal reflection takes `2Q`. A serial word of six admitted reflections then takes `12Q`. | `RootTransferPhase.quarterTime`, `quarter_pulse`, `half_pulse`, `half_pulse_word`. The time unit is the one in `heat_matches`. |
| Certified | The 16-pulse class-blind beta word takes `32Q`. For a certain transfer with every pulse tick-aligned, its quarter-time in substrate ticks is a positive even integer. The minimum elapsed time is 64 ticks and is attained in that clock model. A serial six-reflection word on the same clock raises the bound to 88 ticks. | `ClassBlindFlip.forwardTimes_total`, `certain_quarter_even`, `certain_tick_duration_lower`, `certain_tick_duration_attained`, `certain_with_six_reflections_lower`. The 88-tick bound counts one flip, not two. |
| Certified | The shorter word realizes the completed certain beta flip with 12 pulses taking `24Q`. At one tick per quarter-time, one flip and one six-reflection word take 36 elapsed ticks. | `SplitClassBlindFlip.pulse_completed`, `duration_eq`, `one_tick_budget`. The witness exceeds 32 ticks and fits in 43. |
| Certified | The same-generation glued crossing has a six-reflection word. The equal-class gapped crossing uses four swap reflections and two amplitude parity reflections. It shifts T at `g` to F at `g+2`. | `GluedRegister.crossingWord`, `crossing_word_glued`, `crossing_word_pure`; `GappedGluedCrossing.runSwap`, `runGappedCrossing_encode`, `equalClass_iff`, `forward_entry`. These results give words and endpoints. |
| Certified | The clocked pair retains two requests at consecutive slots. A shared request always returns to its input. For equal marginals `p`, the independent endpoint-change weight needs joint true-true weight `p²`. | `ClockedRootTrials.ticks_zero_one`, `ticks_one_two`, `shared_request_returns`, `matches_independent_trial_weight`. The endpoint-change weight on a moving input is `2(p−j)` for joint weight `j`. |
| Certified | Coherent integer samples alias gaps modulo a full turn. Under independent trials and `0 ≤ p < 1/2`, the two-trial weight `w = 2p(1−p)` identifies `p` and `gap(p) = −log(1−2w)`. | `RootClockCalibration.phase_alias_iff`, `integer_samples_agree`, `ambiguous_exchange_clock`, `trial_weight_inj`, `gap_from_trials`. A calibrated statistical readout or a principal-range witness can distinguish the aliases. |
| Certified | If a statistical pair occupies two coherent substrate ticks, the generator per tick is `G/2`. In that convention the elapsed quarter-time is `π/gap(p)` substrate ticks. | `ClockedRootTrials.heat_after_two_ticks`, `phase_in_ticks`, `exchange_in_ticks_iff`, `principal_weight_in_ticks`. The correspondence of the physical operations is a separate premise. |
| Certified | A common tick cancels from the flip-to-crossing rate ratio. | `CertainTransferRate.common_tick_rate_ratio`. The formula still uses both pulse areas, coefficient conversions and durations. |

## Assumed and open clock inputs

| Status | Input | Consequence |
| --- | --- | --- |
| Assumed | One substrate tick per root quarter-time. | Gives the short-word elapsed budget. It is incompatible with the whole-tick certain 16-pulse word. |
| Assumed | Each reflection in the crossing is a principal half-pulse on the same root clock, and the word runs serially. | Gives two quarter-times per reflection. Discrete crossing support alone supplies no time assignment. |
| Assumed | Each elapsed pulse tick consumes its own active slot in the 32-slot service ledger. | The 36-tick budget then exceeds one frame's service capacity. `PMSubstrate.Clock.schedule_selects_43_of_clock` uses a 32-slot encoding to select the period. It does not route pulses into that encoding. |
| Assumed | The four retained request histories have equal prior counts and both changes have the same local action. | Then actions `0,c,c,2c` give the product Gibbs law. The working tree's `ClockedRootTrials.history_action_additive`, `history_mass_factorizes` and `expected_history_action` check this conditional calculation. |
| Open | Admit and price the comparisons, controlled rotations, crossings and reference renewal on a common clock. | Neither the admissible pulse overlap nor the calibration from statistical-pair time to the physical root tick has been selected. |
| Open | Select pulse areas and their normalizations in the wall Hamiltonian. | The checked endpoint transformations and clock period alone do not identify `K_f` or `y`. |
