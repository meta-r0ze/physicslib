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

## Slot requirements for a wire cycle

Write `q` for the elapsed substrate ticks per quarter-time on a chosen
common root clock. Use half-open intervals `[s,s+d)` for a block of
duration `d` starting at tick `s`. A tick `n` belongs to period
`⌊n/43⌋` and phase `n mod 43`. The table assigns the internal order
and the available timing constraints. The block starts remain variables.

| Event or visit | Scope and certified order | Placement and charge to the clock |
| --- | --- | --- |
| Clock reference excursion and trial pair | In the excursion code the boundaries are phases 0 and 1. The pair uses request 0 at the first boundary and request 1 at the second. | Slots `[0,1)`, `[1,2)` in this code. Sharing those slots or reserving them for wire traffic is open. See `CarrierReferenceCycle.excursion_boundaries` and `ClockedRootTrials.ticks_zero_one`, `ticks_one_two`. |
| Static T in-wall flip | One beta word at the T insertion if the selected event uses the class-blind flip. The charged offset candidate is a separate guarded pulse on T at `g=2` (`ChargedInsertion.joint_selector`). | Start `s_T`. The supplied words use `32q` or `24q` ticks in serial execution. The selected charged offset has no certified clock duration. |
| Reference F in-wall flip | For a direct address the reference permits the bare exchange. A two-leg restoring route supplies the F insertion for the other addresses. | Start `s_F`. The bare direct candidate can use the same beta-word budget. The restoring F operation's duration is open. Charging a separate beta word in addition to the node would require a mapping from the node readout to that word. |
| Equal-class gapped crossing | Four swap steps then two amplitude parity steps on T→F, or the reverse word on F→T. The forward endpoint has address `g+2`. | Start `s_Y`. With serial principal half-pulses, reflection `j` occupies `[s_Y+2jq,s_Y+2(j+1)q)` for `j=0,…,5`. See `runGappedCrossing_encode` and `half_pulse_word`. |
| Class-changing glued crossing | The ordered six-glued-root word gives the same-address endpoint. The heavy guarded variant checks the generation and matching record before it runs. | Start `s_C`. The same serial half-pulse budget applies if admitted. A separate execution costs another `12q`. Which event uses this word in addition to the gapped crossing is open. The endpoints have different support. |
| Reference node passage | For `g=1`, `2→0` enters the reference class. For `g=2`, `0→1` leaves it. In both cases the node has an entry leg followed by an exit leg. For `g=0` the `1→2` insertion is direct. | `ReferenceClassHop.touches_reference_class` and `ReferenceNode.restoring_two_classes` give the route and leg count. The admittance `α/2` fixes no ticks for entry, dwell, exit or renewal. |
| Charged-current doublet record | One position bit per charged-current event. The quark test needs the full static comparison. For lepton it can use the full or lepton-only comparison. One common full visit can serve both requirements if it reaches both. | Record must be available before the event consumes it. See `EventRequirements.pairs_of_sign`, `quark_bit_iff`, `full_reads_both` and `ProtocolToll.lepton_readout_iff`. A full visit also reads the position bit needed by the heavy record at the level of its static truth table. Shared physical preparation, polarity, storage and reuse remain open. |
| Heavy-flip charge record | Two bits if this candidate is used. The electric protocol reads position at charge phase `3π`, then sector at `3π/2` against the matching-position reference. `position_time_minimal` and `sector_time_minimal` bound these parameters in the stated charge-generator units. | A fresh write precedes the selected heavy crossing. Its reuse can move the write to an earlier period. Charge-generator parameters have no proved conversion to this root clock. `HeavyFlipRecords.orbit_record_minimum` counts required logical visits under its premises. |
| Heavy bank preparation, use and reuse | On a supplied seed the short companion setup takes one root on F and two on T. A common two-root setup also works. The fresh inverse-decoder/forward-decoder alternative budgets `27q+25q`. The current-based candidate uses two kicks and an intervening swap. | Prepare before the record write, then hold the record through the guarded event. The inverse decoder pair alone exceeds one period for `q≥1` if serial. The companion transition leaves charged records occupied. Select export, explicit restoration or reuse with a supplied ready record. See `ElectricCompanionSetupToll.short_setup_on_seed_support`, `ElectricCoordinateDecoder.fresh_bank_serial_exceeds_clock` and `ElectricCompanionBank.written_port_ready_iff`. |
| Lightest offset selector | Two matched comparisons on T for each charged target. The selected plus output of the first feeds the retained map of the second. The vector-class test is part of the joint guard. | Both tests precede use of the selected projector. Placement may share a prepared controller only after proving the corresponding joint control and reset. `ChargedInsertion.select_static`, `joint_selector` and `BranchPulseContract.program_correct` supply operators and conditional pulse words. |

Within a beta word, consecutive offsets are the prefix sums of its pulse
durations in application order. Use `ClassBlindFlip.forwardTimes` for the
16-pulse word, or the short word's one- and three-quarter pulses in
`SplitClassBlindFlip`. Matrix products act on column states from right
to left. Pausing between pulses requires the idle dynamics to preserve the
intermediate state.

The available placements in a serial model are all choices of starts
with nonoverlapping intervals and the precedence constraints in the table.
This includes fresh records placed before their first use and records
prepared in a prior period if their persistence is proved. If the Schur
factorization is implemented literally as `R Y⁻¹ A` on a column, its
block order is T, inverse gapped crossing, F. The factorization itself
provides no chronological constraint. At the level of endpoint classes,
`GenerationMass.composite_cross_then_shift` and
`composite_shift_then_cross` exhibit both orderings of a class shift and
a fixed-class crossing. They do not implement a timed scheduler. To
allow simultaneous intervals, supply the independently usable registers,
controls and joint evolution. Clock closure permits both idle and
nonidle masks, so it does not pick an absolute phase for any wire pulse.
