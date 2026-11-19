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

## Selection and the unresolved minimum

`minima` gives the exact finite minimizer set for a supplied scalar cost.
`minima_nonempty` requires a nonempty admitted family.
`best_survival_iff` applies `PersistenceSelection.within_family_iff_cheapest`.
The Gibbs normalization preserves the order of the costs with equal
prior counts (`Gibbs.weight_order`, `probability`). Unequal priors need
their own supply law (`Selection.survivor_odds`).
In the template each fresh required comparison appears once. This is
the Economy case of `RefreshSchedule` and `CoherentRefresh`. The
template does not assume removal of an optional visit preserves physical
admission and the remaining costs.

With both electric output flags paid and other work held out of the
subtotal, `knownToll_recordOnly`, `colour_tolls` and `lepton_tolls`
give the following known budgets.

| Sector reference | Electron | Up | Down | Survival amplitude order for the bit subtotal |
| --- | --- | --- | --- | --- |
| Colour | 2 | 0 | 1 | `s_e < s_d < s_u`. Down is the geometric mean. |
| Lepton | 1 | 1 | 2 | `s_d < s_e = s_u`. Down is not the geometric mean. |

`polarity_tradeoff` proves that neither row minimizes the known Toll
for every charged label. The electron prefers the lepton reference.
Either quark protocol prefers the colour reference. This result does
not require measured values. For a single schedule shared by all
labels a scalar objective needs a rule for weighting the labels.
If the two polarities are both admitted and if that objective is a
weighted sum of bit Tolls plus a remainder, the exact cost difference,
colour minus lepton, is

```text
w_e − w_u − w_d + (remaining_cost_colour − remaining_cost_lepton).
```

By `polarity_minimum_iff`, a negative difference selects the colour
reference, a positive difference selects lepton, and zero ties them.
With equal remainder, a tie needs `w_e = w_u + w_d`. Equal weights per
protocol would favour colour in this two-option calculation. The
substrate results used here supply neither that weighting rule nor
equal remainders. They also leave physical admission of the two
candidates open. If a different template uses a genuinely different
record writer, these two-option inequalities do not compare its cost.

`knownToll_eq_of_paid_eq` proves that changing slots or live branch
while retaining the same polarity and paid visits leaves the subtotal
fixed. If both placements are admitted and their full costs are equal,
`tied_minimum` carries optimality from one to the other. A selection
between those placements needs a phase-specific admission or cost
rule. Dropping a required or unpriced visit would change the physical
premise. In particular, the all-idle clock cannot execute this template.

The light-offset candidate at address two keeps the matched plus
outputs and fires on the stored selector result. Its two paid output
flags contribute zero for each of electron, up and down. The charged
pulse and its remaining account have no selected native firing law.
The vacancy probe has a distinct flag budget `(½,1,½)` in that order.
Economy does not turn that probe into the required selector. The
colour-reference bit subtotal gives the heavy-record pattern only
under the stated assumptions. Neither opposed attenuation pattern
has been selected for the physical wire. The selector supplies no
order of `ε` in `1/Δ`.

## Periods at a minimum

`periodPhase` reads a booked start as a period and a phase.
`periods` rounds up the last occupied end from the fixed clock
origin. `finishTick_le_horizon` bounds it on the finite family.
There is no physically identified minimizer to evaluate.

| Route | Serial base with the short word at one tick per quarter-time | Serial base with the 16-pulse word at its two-tick minimum |
| --- | --- | --- |
| Direct, address 0 | 60 ticks, at least two periods | 152 ticks, at least four periods |
| Enter the reference class, address 1 | 36 ticks plus entry, exit and records. One period requires all added elapsed work to fit seven ticks. | At least 88 ticks before node and records, so at least three periods. |
| Leave the reference class, address 2 | The same 36-tick subtotal. Add the node, records, two matched tests and the offset when running that candidate. | The same 88-tick subtotal and three-period lower bound, before the added events. |

These are the conditional [clock bounds](../PMTransport/CLOCK.md#periods-per-route).
They assume one gapped word and one beta word on each beta-driven wall.
A separate class-changing crossing adds twelve quarter-times. The
logical record counts agree for electron, up and down in this template.
The record Tolls differ, and give no elapsed ticks without a control
clock. Neither equality nor inequality of the full period counts across
protocols follows at a physical minimum.

## Comparison only

- [Down as geometric mean](../../tools/down_mean_check.py). The
  colour-reference two-bit subtotal gives the identity exactly for a
  common price. In the ledger convention the diagnostic gives
  `s_d/√(s_e s_u) = 0.957` and inferred prices 2.043 from electron
  and 2.131 from down. Other conventions give ratios 0.767 to 0.864.
  These inferred prices do not identify a native registration tariff.
- [Tier ratios](../../tools/tier_route_check.py). The declared ledger
  gives `m₁/m₂ = 3/Δ²` for up and about `2.126/Δ` for down.
  The electron value is about `0.208/Δ = 8.94/Δ²` at the fixed
  period. The matched flags provide no power of `1/Δ` for the offset.
- [First-row leakage](../../tools/first_row_readout.py). Under its
  stated readout assumptions the comparison prefers roughly
  `r ≲ 0.07–0.12`. The explored serial-duration options span
  `1/8 ≤ r ≤ 1/2`. The conditional six-reflection ratios `3/8`
  and `1/2` from the [clock ledger](../PMTransport/CLOCK.md#flip-to-crossing-rate)
  exceed that range under equal pulse-area and coupling normalization.
  There is no selected physical `r` to compare.
