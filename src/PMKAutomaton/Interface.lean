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
names refer to `PMKAutomaton/TODO.md`. The physical update is a
client obligation. Phase, branch, reader and work choices appear in
the original hypotheses. See the component contracts in `OVERVIEW.md`.

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

## Interface, clock and admission notes

### Consequences for the wire

| Question | Result of the reachability check |
| --- | --- |
| Writer population | With a common ready reference, `any_incoming_trace` realizes any supplied live arrival sequence in the open model. The restored live port contains the reference, and the displaced record port contains that sequence. The node law is compatible with different traffic and does not identify the writer's input port. `VacancyProjection.occupied_fixed_iff` excludes the sterile basis slot from occupied payloads. It leaves idle bookings and active probes open. None of the three uniform policies is forced. |
| Heavy branch | `HeavyFlipControl.direct_iff` gives address zero. `no_root_only_direct_address` excludes a guard that reads only the untagged glued root. `ElectricCompanionBank.guarded_companion_transport` gives the candidate with the prepared tag and electric record. The joint controller must supply and retain the tag on the direct wall and fire the guarded crossing. The two reference polarities remain candidates. |
| Lightest-offset branch | `ChargedInsertion.joint_selector` has support only at address two on a matching charged static label. `matched_flags_zero` gives zero flags on the two matched comparisons. It leaves their control and the offset firing open. The joint controller must retain their plus records and bind them and the static vector test to the pulse. |
| Trial priors | The same update gives four histories with one state per pair and two histories with one state per shared request. Physical equality requires the accessible finite controller background and its request fibres. |
| Physical schedule | The trial slots are fixed in the stated experiment. The wire's operation order, overlaps and times of repeat visits need a joint controller and boundary supply. |

**Record reference undetermined.** For two admitted writers with a
common booked population, let `M_L` and `M_C` be the booked colourless
and coloured input masses. The output flag difference is
`G = M_L − M_C` by `WireReferenceCost.booked_population_difference`.
If both writers also pay a separate balanced reset per independent
bit, `booked_balanced_reset_difference` gives the total signed
colour-minus-lepton cost `U + (3/2)(M_L − M_C)`. Here `U` is the
difference in remaining paid work, in the same units. Its sign
selects colour when negative, ties at zero and selects lepton when
positive, provided both schedules are admitted.

The [three reset-inclusive thresholds](../PMElementaryParticles/WireSchedule.lean)
are conditional cases of this account. The decisive missing inputs
are the booked traffic and polarity traces from **Background occupancy
and boundary supply** and the **Joint clocked controller**, followed
by the signed remainder under the [Registration tariff](TODO.md#clock-and-accounting).
For this decision only, under a common population it suffices to give
the signed sector mass difference and enough unmatched paid work to
bound the total on one side of zero. If the two admitted polarities
use different traffic, compute the two weighted charges separately.

### Downstream scope

[The top-down filter](OVERVIEW.md#component-contracts) keeps both
equivariant conserving bank witnesses under the certified cellwise
action. [The least-Toll test](OVERVIEW.md#cost)
selects only within a supplied physical booking. The mixed receiver
gap and the scoped tagged symmetry therefore remain.

The [joint lift](OVERVIEW.md#component-contracts) projects
to these exact core traces. Its packet bank has a certified FIFO
permutation. The projection supplies no physical FIFO firing time
or packet operator. The [fan-out result](OVERVIEW.md#component-contracts)
puts the routed pair and computed comparison in one receiver
stencil. A clocked EP attachment and detector support are still
required to use either one. The retained core routes its values
without booking that comparison.


The [downstream audit](OVERVIEW.md#component-contracts) separates fixed values and
formulae from observations of receiver traces. **Symmetry.**
`LocalController.tagged_ticks_equal` and
`tagged_trace_observable_eq` cover every common read of the full
tagged trace, including its clock and controller fields. A common
erasure projection and supplied prior therefore give equal
merged weights there.

**Excluded.** A quotient of the unrestricted machine by AND/OR
would forget different destinations and receiver flags.
`mixed_open_receiver_destinations` and
`RingReceiver.mixed_ring_flags` exhibit the difference at the
same input, before disposal. No certified EP consumer maps that
mixed trace to a writer or insertion.

**Conditional.** If such a trace is read, keep its routed value
and destination or its executed comparison and booked flag
through the relevant read. The missing choice is which of these
observations a writer or insertion consumes. It bears on writer
population and on the Toll in the wire amplitude. The
[admission contract](TODO.md#admission-and-ports).

**Derived.** The no-export ring's erasure weights give the
normalized supplied prior. **Conditional.** For reset erasure
the electric-reference threshold needs the difference of the
writers' booked erase counts. See the
[prior and reset checks](OVERVIEW.md#component-contracts).

### Assumed and open clock inputs

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

### Slot requirements for a wire cycle

These bounds describe the supplied serial words and named layouts. The retired EP restoring-capacity mass route used some of these schedules. The clock certificates remain conditional on the stated word and clock.

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
`GenerationDiagonal.composite_cross_then_shift` and
`composite_shift_then_cross` exhibit both orderings of a class shift and
a fixed-class crossing. They do not implement a timed scheduler. To
allow simultaneous intervals, supply the independently usable registers,
controls and joint evolution. Clock closure permits both idle and
nonidle masks, so it does not pick an absolute phase for any wire pulse.

### Which branch drives each pulse

These bounds describe the supplied serial words and named layouts. The retired EP restoring-capacity mass route used some of these schedules. The clock certificates remain conditional on the stated word and clock.

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
`EffectiveAction.attenuationWeight` at unit scale.

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

### Readout consumption

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

### Remaining free inputs by reach

Only KAutomaton machine inputs are ranked. Protocol inputs and the protocol
halves of split inputs are removed to EP; see the section below.

| Input | Output count | Affected outputs |
| --- | ---: | --- |
| T · Clock placement and calibration | 6 | Physical schedule, elapsed route periods, physical `r`, heavy crossing, lightest insertion, read availability. |
| U · Common comparator and record port | 4 | Receiver record-port comparison, writer population, heavy crossing, insertion amplitude. The label record, reference and theta are EP. |
| K · Tariff unit and amplitude conversion | 4 | Per-registration price, wire amplitude, substrate-index reconciliation, reference threshold. The label Toll and paid-event choice are EP. |
| B · Export and disposition | 4 | Erased bits per period, renewed readiness, merged-history weights, erasure-reset threshold. |
| D · Detector support | 4 | Registration count, receiver Toll, insertion amplitude, calibration statistic. |
| J · Shared jobs and contention | 3 | Physical schedule, incremental maintenance Toll, reused jobs. |
| Q · Reference supply and acceptance | 3 | Clean visits, sustained renewal, heavy bank readiness. The reference record choice is EP. |
| L · Admitted link and successor law | 2 | Realized route, effective through weight. |

Layering is a separate build decision in [the open list](OVERVIEW.md#native-machine).
It supplies no physical input to this ranking.

**Certified coin (Task L).** The converter's pass/flip amplitudes are
`(1 ± e^{ix})/2` (`PhaseToRecord.converter_plus`, `converter_minus`), i.e.
`cos(x/2)`/`sin(x/2)` up to phase. `encounter_unitary` is the coherent
one-site encounter; `exact_bit_flip` gives the `x=π` full flip. The full-ring
Lean block spectrum was not completed; the script verifies
`cos E(k) = cos(x/2) cos k` exactly, with gap `x` and gapless empty firing.
The mass interpretation is a hypothesis. The conditional interface leaves these inputs open: T, L, B, D, J, Q and the tariff unit remain named
machine inputs.

**Phase-to-record converter (Task K).** `CoherentComparisonRepair.compare (phase x)`
is a certified unitary (`PhaseToRecord.converter_unitary`). Its minus output has
probability `DiagonalReadout.flag x` (`minus_probability`), the expected receiver
flag is `flag x` (`expected_receiver_flag`), and the converted branch records are
orthogonal (`converted_records_orthogonal`, `converted_branch_records_unequal`).
`bitToll_eq_expected_conversion` recovers the EP row. The factor-two normalization
is the phase encoding (`nsq/4`) versus orthogonal receiver encoding (`nsq/2`).
Gap U's flag identification is closed for all phases; no new unitary was defined.
The physical port wiring remains part of the admitted trace, not a new choice.

**Common comparator status.** KAutomaton's receiver-flag computation W and the
guard table G are certified and removed from the open ranking:
`LocalController.receiver_flag_eq` and
`IsolatedReceiverTrace.localized_period_registrations_eq` give W;
`RingReceiver.tick` and `receiver_flag_eq` give G.

The receiver and electric flags share the `CommonResponse` parent only up to
normalization. `CommonResponse.stateFlag U φ = nsq (φ - Uφ)/4`;
`DiagonalReadout.flag x = (1 - cos x)/2` and
`DiagonalReadout.state_flag` expresses the diagonal transport flag as the
`|φ_c|²`-weighted mean. `CommonComparator.exchangeFlag_eq_two_linkFlag` shows
the receiver comparison is twice `CommonResponse.linkFlag` of the identity,
while `CommonComparator.flag_eq_stateFlag` shows the electric flag is
`CommonResponse.stateFlag` of the unit phase. The EP exact record bits are
`DiagonalReadout.flag` values from `ElectricHeavyRecord` and
`bitToll_eq_hamming`. This is a common parent, not an exact identification:
the factor-two normalization remains. Gap U is not closed.

**Protocol inputs moved to EP.** EP owns the retained request field and firing
pattern (G), the excitation occupancy and reference-record choice (O), the
label record/reference/theta part of U, which label record W reads, and the
label Toll/paid-event part of K, plus the history/prior family H. The certified
label dependence is `bitToll_eq_hamming`, `refRecord`, `bitRingTotal43_eq` and
`firingPattern`; these are protocol data, not machine data.

**Next priority (KAutomaton only).** Finish the common comparator behind the
machine half of U, certify the coherent receiver exchange as a root-transfer
pulse of area theta, and settle the remaining T/L/B/K machine questions. The
record-port identification, reference selection, firing requirement and
checkerboard amplitude belong to EP, not KAutomaton.

**Isolated-excitation input.** `PMElementaryParticles.IsolatedExcitation`
fixes O for the object a mass refers to: the stationary E8 background plus
one packet label. `IsolatedReceiverTrace` keeps two separate fields. The
uniform field puts the packet on all sites and both streams; its occupancy is
six and it is not one excitation. The localized field has one live packet at
one site, record vacuum there, and vacuum elsewhere; its occupancy is checked
and preserved by `tick`. Requests are retained; the port field has period 12.
The localized 43-tick receiver sum is `patternSum (firingPattern either r) x0`
(`localizedSum43_eq_pattern`). AND and OR differ exactly when their pattern
table entries differ (`localized_and_or_differ_iff`). The record Toll remains a
separate column. The hold/FIFO lifts do not determine booking ticks.

### What propagates downstream

G remains open. The top-down checks narrow the admissible fibre
actions by equivariance and conservation, and leave at least the
hold/FIFO witness pair in the certified interface. The previous
[reach ranking](OVERVIEW.md#component-contracts) therefore still
applies. Distinct outputs remain possible even at tied booked cost.

| Input | Narrowed interface | Still needed |
| --- | --- | --- |
| W, attachment | A common read on a common tagged trace is invariant. Mixed receiver outputs and computed flags are local. | Name the live, record or comparison result read by the writer, and its tick. |
| B, export | Identity stays bijective when a separate output is disposed of. Tagged exports agree under common disposal. The encoded ring exports zero. | Identify the physical booked output and disposition, including reset and return wiring. |
| U, carrier to EP | The channel action and conserved totals are explicit on a 16-slot bank. | Intertwine the actual carrier operation and EP label/reader on the same admitted trace. |
| D, detector | A common mask gives the exact conditional mixed flag rate. | Identify the occupied detector support, reader and booking. |

No input in this table is closed on untagged physical traffic.

**Export contract.** The fixed values in `Values` and `Interface` have no
receiver-rule argument: they are the same functions at the same arguments. A mixed
receiver trace can differ only in its routed value and destination, or in the
executed comparison and its booked flag. No certified EP trace consumes either
datum. A consumer that needs one must expose the equivalent route information and
keep the destination or branch available through its last use; a flag rate or
survival amplitude alone needs only the booked comparison.

The no-export ring leaves the supplied prior normalized
(`BoundaryErasure.ring_erasure_survivor_eq`). For reset erasure the
electric-reference threshold is `B − (E_C − E_L)`
(`WireReferenceCost.reference_threshold_with_erasure`), where `B` is the output
flag threshold and `E_C − E_L` the difference in booked erased bits. The old
`3/4`, `27/32`, `9/10` values therefore require `E_C − E_L = −B/2` in the
replacement account; the certified tagged train gives no such export-count
difference.

### KAutomaton closeout

The conditional interface is complete for the certified operations.
Use `PMKAutomaton.Interface` for their original laws and
`PMKAutomaton.Values` for rates and thresholds with booking, work and
erasure inputs visible. The physical joint update and EP admission
remain open.

| Certified interface | Physical contract left to the caller | Why the present laws leave it open |
| --- | --- | --- |
| Embedded Weyl generators and marked edge groups | L/G/U. Give the marked geometry and its simultaneous action on core and packet. | Different marked edge stabilizers and the probe obstruction. See [bare-line stabilizer](OVERVIEW.md#bare-line-stabilizer). |
| Reversible controller, conditional FIFO and conservation | G/T/O. Give the admitted fibre operation, ticks and initial traffic. | Two distinct conserving equivariant bank operations over the same core. Distinct excursion masks share a period and minimum cost. |
| Tagged symmetry and computed receiver output | W/D/U. Give the reader, clocked detector support and label embedding. | The mixed destinations and flag differ and share a local stencil. |
| Open restoration, records and terminal erasure | Q/B/J. Give continuing ready inputs, booked outputs and any reuse/contending jobs. | Exact results require supplied reference and export contracts. The retained ring has no disposal event. |
| Expected booked work, conditional minimum and survival | K/H. Identify distinct physical events, rates and priors. | The units and ordering are fixed on a supplied trace. The classified operations do not choose its event list or accessible masses. |

EP can use the rate and amplitude laws on a specified trace. The
booked mixed comparison uses `mixed_and_survives_iff`. A balanced
reference-reset threshold can be used for a boundary erasure
account only under `erasure_reset_matches_balanced_iff`.
The [EP occupancy-cost task](../PMElementaryParticles/TODO.md#occupancy-cost) needs a physical recurring trace and a capacity unit. The interface supplies the conditional rate and accounting laws for that trace. The [ranked ledger](OVERVIEW.md#component-contracts)
retains all 12 entries.
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

/-- With the through stream as the untransferred port, a principal-range
exchange pulse that realizes the geometric admittance has this area. -/
theorem principal_through_area_eq (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ Real.pi / 2)
    (h : ∀ nL nR, leftOutflow (Real.cos t ^ 2) nL nR - nL =
      PMSubstrate.causalCoupling * (nR - nL)) :
    t = Real.arccos (Real.sqrt PMSubstrate.causalCoupling) :=
  PMAction.CertainTransferRate.principal_through_area ht ht' (through_weight_eq_alpha t h)

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
export PMAction.TollAmplitude (weightedFlagCost rare_registration_limit unflagged_scale
  wireAmplitude_sq wireAmplitude_lt_iff amplitude_ratio
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
  all_pairs_history_count shared_request_history_count history_pmf_factorizes
  matches_independent_trial_weight heat_after_two_ticks phase_in_ticks)
export PMAction.CertainTransferRate (certain_min common_tick_rate_ratio principal_transfer_area
  principal_through_area principal_transfer_rate_ratio)

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
