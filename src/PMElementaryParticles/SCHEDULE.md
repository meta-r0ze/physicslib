# Persistence selection on the wire

## Admissible candidates

[Clock ledger](../PMTransport/CLOCK.md) records the available words.
[Generations](GENERATIONS.md) records their address and label support.
`WireSchedule.family` enumerates a bounded, serial, fresh-record
template for one cycle at a supplied glue address. A candidate stores a
start tick, live port and registration bit for each present block. It
also stores the sector-reference polarity. Unused blocks are absent.
The start tick encodes both its period and its phase.

| Constraint | Source or premise |
| --- | --- |
| Static word and one gapped crossing; reference word on zero, two node legs on the other addresses | `HeavyFlipControl.direct_iff`, `ReferenceNode.restoring_two_classes`, `GappedGluedCrossing.runGappedCrossing_encode`. The use of the words as successive physical insertions is the literal serial Schur-order premise. |
| Flip lengths and crossing budget | `SplitClassBlindFlip.duration_eq`, `ClassBlindFlip.forwardTimes_total`, `certain_quarter_even`, `RootTransferPhase.half_pulse_word`. The common quarter-time and the use of principal half-pulses for crossings are premises. |
| Fresh heavy record precedes its controlled insertion | `HeavyFlipControl.registered_word`, `ElectricHeavyRecord.phase_position`, `phase_sector`, `phase_sector_lepton_reference`. The template uses the two-visit electric writer and both polarities. Its identification with the firing at the reference insertion is a premise. |
| If a charged-current event is present, one full doublet visit precedes it | `EventRequirements.pairs_of_sign`, `full_reads_both`. Using the full readout on both wall populations is the chosen record template. |
| The address-two candidate has two matched tests followed by the offset | `ChargedInsertion.select_static`, `joint_selector`, `matched_flags_zero`. The tests keep the plus port. The offset needs the selected record and a supplied trigger. |
| Optional setup, class-changing crossing, export, renewal and vacancy comparison | The template may include them. Placement, physical admission, repetition across cycles and what the register supplies are premises. The vacancy probe does not replace either matched test. |
| Bounded start times, positive block durations, no overlap | Finite horizon and serial execution premises. A Boolean admission test supplies phase availability, reset or export, viable seed supply, branch constraints and ownership of each paid visit. |

The family is executable given these finite inputs. It does not quotient
by colour, wall exchange or class cycles. In particular the reference
distinguishes addresses and the ready bank distinguishes some wall
states. Other writers, multiple instances of one block, prewritten
records and parallel schedules are outside this template. No premise
identifies it with the full family of persistent E8 executions.

## Pricing

`visitFlag` uses `DiagonalReadout.flag` for the electric position and
sector visits. It uses `EventRequirements.massiveFlag` for a full
doublet visit with equal wall populations, as justified by `massive_flag`.
A separate vacancy probe has the uncompensated flags at `3π/4`
(`ProtocolToll.selector_step_flags`). The two matched visits, evaluated
on their selected static input, contribute zero by `matched_flag_account`.
A setup placed on the certified equal-slot companion program uses its
primitive flag account (`ElectricCompanionSetupToll.equal_slot_setup_sum`).
Other setup implementations have an unpriced account.

`knownToll` adds the proved flags only where the schedule charges the
visit. `unpricedVisits` identifies marked visits without a flag
certificate. `fullToll` also takes an explicit remainder for unpriced
primitive work, seed supply, export, restoration, renewal and controller
work. These costs can matter even if the comparison's output flag is zero.
No remainder is assigned. Comparison-output flags and primitive-factor
flags can describe different accounts of the same visit. The template
uses the former for the writer and does not also charge the full factor
ledger for that writer. The registration policy must justify any extra
primitive charge. `amplitude` applies `TollAmplitude.wireAmplitude`
to the full Toll for the persisting unflagged readout.
