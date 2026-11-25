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

## Root calibration

A moving label reads the full complex phase of the reconstructed pulse.
Gaps π and 3π give the same coherent history at integer ticks, including
a reflection on the first tick. See `phase_alias_iff`,
`integer_samples_agree` and `ambiguous_exchange_clock`.

A two-trial test can instead read the probability on the two record-port
labels of the prepared vector-class odd live seed
(`RootClockCalibration.odd_seed_trial_weight`). In statistical-pair time,
a reflection at elapsed time `N` requires `−N log(1−2w) = π + 2πk`. The
principal calibration gives `w = (1 − exp(−π/N))/2` and can also use a
coherent flag on the principal range (`exchange_tick_iff`,
`principal_trial_weight`, `principal_flag_inj`).

The reference excursion retains the request bits and advances to phase
2. A moved input changes exactly when the bits differ
(`ClockedRootTrials.pair_endpoint`, `shared_fire`). With the same
statistical pair occupying two substrate ticks, the coherent reflection
test becomes `−N log(1−2w)/2 = π + 2πk`. Its principal weight is
`(1 − exp(−2π/N))/2` (`exchange_in_ticks_iff`, `principal_weight_in_ticks`).

On a moving input, the action that charges each change in the two-tick
trace at the same supplied price `c` takes the values `0, c, c, 2c` on
the four retained histories. The idle and double-fire histories have the
same endpoint and different actions for nonzero `c`. The equal-prior
Gibbs law for these four histories factorizes, with each slot's rate
`p = exp(−βc)/(1 + exp(−βc))`. The expected action is `2cp`, and the
endpoint-change weight is `2p(1−p)` (`history_action_additive`,
`no_endpoint_action`, `history_mass_factorizes`,
`expected_history_action`, `history_endpoint_weight`).

The physical protocol still needs to admit the four equally counted
histories, identify and price the two local registrations, and place its
coherent pulse on the same clock.

The isolated trial's requests persist unchanged. Its carrier is idle
in phases 2–42 (`iterate_controls`, `quiet_trial_tick`,
`trial_period_endpoint`). The [admission check](ADMISSION.md#exhaustive-trial-histories-and-conditional-counts)
enumerates the four retained pairs. The shared-request preparation
has only the two equal-bit histories. Physical prior counts require
the actual controller background.

## Assumed and open clock inputs

| Status | Input | Consequence |
| --- | --- | --- |
| Assumed | One substrate tick per root quarter-time. | Gives the short-word elapsed budget. It is incompatible with the whole-tick certain 16-pulse word. |
| Assumed | Each reflection in the crossing is a principal half-pulse on the same root clock, and the word runs serially. | Gives two quarter-times per reflection. Discrete crossing support alone supplies no time assignment. |
| Assumed | Each elapsed pulse tick consumes its own active slot in the 32-slot service ledger. | The 36-tick budget then exceeds one frame's service capacity. `PMSubstrate.Clock.schedule_selects_43_of_clock` uses a 32-slot encoding to select the period. It does not route pulses into that encoding. |
| Assumed | The four retained request histories have equal prior counts and both changes have the same local action. | Then actions `0,c,c,2c` give the product Gibbs law. The conditional calculation requires Admission and the Registration tariff. |
| Open | Admit and price the comparisons, controlled rotations, crossings and reference renewal on a common clock. | Neither the admissible pulse overlap nor the calibration from statistical-pair time to the physical root tick has been selected. |
| Open | Select pulse areas and their normalizations in the wall Hamiltonian. | The checked endpoint transformations and clock period alone do not identify `K_f` or `y`. |

`ClassBlindFlip`, `RootCliffordCompletion`, `CompletedCarrierPhase`
and `SelectiveCarrierRouting` give candidate controls and endpoints for
the calibrated word. A physical common clock would feed
`LightLeakage` and `SplitClockBoundary`.

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

## Periods per route

Count elapsed serial ticks, with carry across periods allowed. For a
block total of `B` whole ticks, a frame-aligned start and exclusive
use of the elapsed clock require at least `⌈B/43⌉` periods. A start at
phase `h` with `0 ≤ h < 43` touches at least `⌈(h+B)/43⌉` periods
when `B>0`. Gaps and guards can increase either bound.

The table uses one gapped crossing and serial whole-tick beta words.
The direct route uses one word on each wall. For the two restoring
routes the node performs the F insertion. `L₁,L₂` stand for the
whole-tick budgets of their entry, dwell and exit, if admitted. All
records, setup, optional fixed-clock reservations and reference renewal
are additional. Each entry is a base budget at the respective minimum
permitted quarter-time.

| Route | With the short word at `q=1` | With the 16-pulse word at `q=2` | Can the full route fit in one 43-tick period? |
| --- | --- | --- | --- |
| Direct `g=0` | `24+12+24 = 60`, at least 2 periods | `64+24+64 = 152`, at least 4 periods | Excluded for this serial two-word implementation, for electron, up and down. |
| Enter the reference class, `g=1` | `36+L₁`. At least 2 periods if node and added work together exceed 7 ticks. | `88+L₁`, at least 3 periods | The short word leaves at most 7 elapsed ticks for the node and all additional work. The long word excludes one period. |
| Leave the reference class, `g=2` | `36+L₂`, with the same 7-tick available budget | `88+L₂`, at least 3 periods | The same exclusions apply. Admittance symmetry establishes no equality of `L₁` and `L₂`. |

If the cycle also executes a separate class-changing crossing, add
`12q`. The direct totals then become 72 and 176, requiring at least
2 and 5 elapsed periods. The restoring subtotals then become 48 and 112
before either node duration, so the short-word one-period option is also
excluded. If an implementation adds a separate beta word at F on a
restoring route, it pays that word's duration as well.

| Logical work if the event is required in the period | Electron | Up | Down |
| --- | --- | --- | --- |
| Charged-current doublet bit | One full or lepton-only visit | One full visit | One full visit |
| Heavy fresh record on the direct address | Two bit visits | Two bit visits | Two bit visits |
| Charged-offset projector at the static vector address | Two matched tests | Two matched tests | Two matched tests |

Timing for those visits and for their reset is still open. The logical
counts come from the slot table. A zero flag on a label does not remove
the corresponding visit from an execution that applies the comparison.
If a fresh inverse-decoder/forward-decoder record is required serially on
the direct route, it adds `52q`. Even with one crossing the base totals
become 112 ticks at `q=1` and 256 at `q=2`, before kicks and reuse.
This gives lower bounds of 3 and 6 periods for that particular record
choice, equally for all three charged protocols.

Under the additional active-slot rule, every serial base budget in the
route table exceeds 32, even the 36-tick short restoring subtotal.
With 11 idle phases and no adjacent idles, the cyclic active mask has
11 nonempty runs. The longest contains at most `32−10 = 22` ticks.
Thus an uninterrupted 24-tick flip cannot stay in active slots on
such a mask, even across the period boundary. A scheduler could allow
idle gaps between primitive pulses if it proves the state is held.
Counts alone would leave the alignment of those pulses open.

If the wall flips can run concurrently, two short 24-tick flips followed
or preceded by one 12-tick crossing have a 36-tick elapsed budget.
That arithmetic does not admit a parallel update. Requiring the
gapped crossing between successive operations on one amplitude instead
precludes overlapping those operations. The library leaves the
physical choice between these executions open. It derives neither a
minimum full-route period count nor a protocol-dependent one.

## Which branch drives each pulse

`CoherentGate.unequal_needs_orthogonal` requires orthogonal records
when the two weak outputs would otherwise overlap.
`RefreshMap.asymmetric_gate_records` gives the discrete version. These
results determine which inputs the record must distinguish. Either
polarity preserves this distinction. A reversible controlled gate can
use either branch if the branch basis is exchanged and the controls
are relabelled with it. In block form, conjugating `diag(I,U)` by the
branch swap changes it to `diag(U,I)`. The `RegisterControl` encoding
preserves the choice of control supplied to it. Conservation therefore
does not decide which record value drives the physical pulse.

| Event or visit | Branch fixed in the specified circuit | What the physical schedule still needs |
| --- | --- | --- |
| Reference excursion and trial pair | The phase boundary and retained request control the reflection. A false request leaves the carrier idle at that slot. | A source of the requests and a registration test. A double fire can return to the same endpoint and still move twice. |
| Bare beta and bare crossing words | Each word acts on its whole supplied carrier input. Intermediate coherent pulses evolve both components of that input. | A physical trigger and a proof that the relevant address, chirality and input bank see the word on the chosen clock. |
| Through the reference node | The reversible handoff model sends the two results to different registers. Bypass goes through. Exchange gives the returning route and restores the receiver when the arriving record supplies its reference (`TwoSiteHandoff.step_trace`, `first_reference_iff`, `receiver_agrees_with_line`, `HandoffAdmittance.receiver_exchange_or_bypass`). | An identification of these results with the reference-class insertion and a branch-resolved record and renewal trace. |
| Charged-current comparison | In the full static readout, electron and down write the minus outcome, up and vacancy the plus outcome. The charged-current event depends on the stored doublet bit. | Which mixed-wall input and which visits occur in the physical event. Both bit values can serve their own events. |
| Heavy guarded endpoint | In `HeavyFlipControl.registered_word`, the matching stored record at the direct address drives the crossing. The record bits and the address persist. It can be the all-zero record or a record containing a flag. `CompanionHeavyFlip.run_pack` checks a companion-based guard with the same conditional endpoint. | A write, export and reuse schedule and an identification of this endpoint control with each physical heavy insertion. |
| Lightest offset | The candidate retains the plus output at each matched comparison. `matched_flags_zero` gives zero flags for the selected static input. Its joint class and protocol control acts only if a pulse is supplied. | Admit and fire that conditioned pulse. A vacancy-relative minus event is a different comparison. |
| Comparison implementation and repair | In `BranchPulseContract.program_correct`, `ctrl U` applies `U` on the internal second branch between mixers. The minus flag is an output of the entire comparison. Coherent uncomputation restores the prepared input together with the record (`CoherentComparisonRepair.prepared_uncompute`). | Scheduled prices, physical record export or reset, and a rule for which output history continues on the wire. The inverse generally acts on unflagged inputs too (`inverse_not_flag_only`). |

The flag budgets below count the stated visits. A flag becomes a paid
registration only with the stated tariff and branch accounting.
Boundary erasure needs an exported bit booked for reset. A paid
unflagged schedule keeps amplitude `exp(−T/2)` under
`TollAmplitude.wireAmplitude`.

| Conditional accounting | Electron | Up | Down | Consequence |
| --- | --- | --- | --- | --- |
| One uncompensated vacancy comparison | ½ | 1 | ½ | Up has the greatest attenuation under a common positive price. |
| One visit per heavy orbit bit, with the colour reference | 2 | 0 | 1 | Up has the least attenuation. `ElectricHeavyRecord.colour_reference_toll` agrees with `HeavyFlipRecords.orbit_record_tolls` for this choice. |
| Two matched static tests for the selected light offset | 0 | 0 | 0 | These two selected output flags supply no label-dependent attenuation. |
| Own-event charged-current flags | 1 | 0 | 1 | Electron and down tie (`EventRequirements.own_event_tolls`). One common full visit on equal wall populations also ties them, with flags ¾, ¼ and ¾ (`full_massive`). |

The exact charge record can also use a lepton sector reference. It
changes the budgets to `1, 1, 2` in the same charged order, with the
same stated phase durations (`ElectricHeavyRecord.lepton_reference_toll`).
Exact record writing and the timing budget therefore leave even this
polarity open.

The route and period bounds select none of these budgets as the physical
Toll. Even which operation pays matters. For example, a shared factor on
both wire flips cancels from mass ratios, whereas damping only the node
legs raises the relative heavy weight
(`EventRequirements.uniform_weight_cancels`, `node_toll_raises_heavy`).
A permanent record can change the timing without changing its truth
table. The missing result is a joint clocked trace that supplies the
occupied reference and record, admits the pulse, and identifies which
histories are counted and which drive each wall's insertion.

The nominal serial minimum counts are also available in
`PMKAutomaton.Values`. The restoring counts are subtotals before node
and record work.

## Flip-to-crossing rate

Let `A_f,A_y` be the effective pulse areas and `c_f,c_y` the conversions
from pulse rates to Hamiltonian coefficients. Let `d_f,d_y` be the
durations of the individual flip and crossing. With one common tick,
`CertainTransferRate.common_tick_rate_ratio` gives

```text
r = K_f / |y| = (c_f / c_y)(A_f / A_y)(d_y / d_f).
```

In the serial half-pulse execution of either six-reflection crossing,
`d_y = 12q`. The supplied flip durations are `32q` and `24q`. Thus the
conditional duration ratios are `3/8` and `1/2`, respectively. They
give `r` itself if both complete events have equal effective areas and
coefficient conversions. The denominator here is the duration of one
flip. The two-wall cycle budget, record overhead and elapsed time
between firings measure different quantities. Assigning the same area
or duration law to a node-mediated insertion would need its own
derivation. So the current results give conditional ratios and leave
the physical `r` open.

### Comparison only

The recorded first-row wall-leakage diagnostic prefers
`r ≲ 0.07–0.12` with its stated spectral and readout assumptions. The
explored duration options span `1/8 ≤ r ≤ 1/2`. The two conditional
six-reflection ratios above are above the preferred range under equal
normalization. Neither number selects a pulse, a clock, or a record.
See [first-row wall leakage](../PMFlavor/TODO.md#first-row-wall-leakage)
and the [EP readout comparison](../PMElementaryParticles/OVERVIEW.md#charged-density-and-wall-leakage).
