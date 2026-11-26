import PMElementaryParticles.ElectricHeavyRecord
import PMElementaryParticles.ChargedInsertion
import PMElementaryParticles.ElectricCompanionSetupToll
import PMKAutomaton.Interface

/-!
# Finite serial wire-cycle candidates

A bounded family for the literal Schur order with the exact two-visit
electric writer. It represents a cycle at one glue address. Other record
writers and simultaneous pulses would need different execution templates.
The finite search does not supply physical gate admission, tick calibration,
or a registration policy.

## Persistence selection on the wire

## Admissible candidates

[Clock ledger](../PMKAutomaton/OVERVIEW.md#clock) records the available words.
[Generations](OVERVIEW.md#generations-on-the-e8-wire) records their address and label support.
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
primitive charge. `amplitude` applies `PersistenceMechanics.EffectiveAction.attenuationWeight 1`
to the full Toll for the persisting unflagged readout.

## Which population is charged

`NetCost.prob` assigns the uniform measure once the cycle sample space
`Ω` has been specified. `expected_count_linear` adds event probabilities.
`TollAmplitude` converts a given label's expected registrations to an
amplitude. It supplies no rule for choosing the inputs to a shared
comparison or aggregating their Tolls.

`WireReferenceCost.packet_flag` specializes `DiagonalReadout.state_flag`.
The flag of a packet state is the sum of the diagonal flags weighted by
its actual slot populations. `massive_pair_flag` gives half weight to
each wall within one massive input as in `EventRequirements.massive_flag`.
This does not determine how often that input is used. The electric
generator and the hypercharge transport are diagonal. Their action on the
whole packet establishes the available flags and leaves input sampling
open.

| Input | Active slots | Static slots | Probability under full-packet uniform sampling |
| --- | --- | --- | --- |
| Electron | 1 | 1 | 2/16 |
| Down | 3 | 3 | 6/16 |
| Up | 3 | 3 | 6/16 |
| Neutrino | 1 | 0 | 1/16 |
| Sterile vacancy | 0 | 1 | 1/16 |

`wall_inventory` and `uniform_slot_weights` check the table from
`ProtocolInventory`. Each quark has one slot per colour on each wall.
Replacing a sampled charged pair by its massive state preserves its
expected flag if its two slot weights are equal and summed into the
pair's total weight. The neutral active slot and the sterile label
are distinct inventory entries. The full-slot ensemble samples the
vacancy. An occupied-only ensemble excludes it and conditions on the
other slots.

The library proves two relevant conditional uniformity results.
`uniform_if_inherited` uses the transitive symmetry of the 32 substrate
carriers and `PreparationSelection.packet_preparation_uniform`. It
requires that the writer inherits that invariant law on the packet.
`uniform_if_maximin` applies `PersistenceMaximin.maximin_iff` if the
writer guarantees worst-case return over all 16 slots. Neither the
fixed electric comparisons, the charged two-wall populations, nor
the schedule's least-cost selection proves either premise. The missing
physical identification is which incoming states actually reach these
writer visits and whether the cycle cost is a sampled expectation or
an additive ledger of separately required reads.

### What the open receiver supplies

`OpenHandoff.receiver_trace` brings the reference from the positive
input line and displaces the live arrival from the negative line into
the record. `export_trace` tracks that displaced value at each
downstream record address. `acceptance_iff_supply` tests only the
positive input line. `RecordSupply.lattice_forever` keeps that
reference when the backward orbit is open and already supplied.

`OpenHandoff.any_incoming_trace` proves that an exactly supplied
open receiver permits every live arrival sequence in this model.
The same reference can therefore accompany different label
frequencies. This witness concerns the transport update and
does not admit any particular physical source. At the restored
live port the next operation sees the supplied reference. At the
displaced record port it sees the incoming live value. The heavy
direct address avoids the reference class
(`HeavyFlipControl.direct_iff`). None of these facts attaches its
writer to either receiver port or the bypass stream.

If the writer receives only occupied light payloads, the static
vacancy has no incoming population (`VacancyProjection.occupied_fixed_iff`).
A clock or a controller can still book a vacant visit or probe
the vacant basis slot. No theorem here maps the actual live
arrivals and the writer guard to all 16 slots, an idle-vacancy
cadence, or uniform sampling of the 15 occupied slots. The missing
input is the admitted joint source, routing and firing law on
the live stream. It must say what counts as a writer visit and
which ensemble of visits enters the cost. The reference supply
law cannot replace it.

The [KAutomaton closeout](../PMKAutomaton/OVERVIEW.md#kautomaton-closeout)
identifies the scope of tagged symmetry, mixed-input differences
and the conditional rates. O supplies the writer population and H
its prior. G, U and W attach the writer to a clocked operation on
that population. See the [EP blockers](TODO.md).

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
for every charged label. The position flag agrees across references.
The sector flag reverses. `WireReferenceCost.bitToll_difference`
gives `+1` for each colourless slot and `−1` for each coloured slot.
For a normalized population that runs the reader on its support,
`population_difference` gives the expected difference, colour minus
lepton, as `2 p_colourless − 1`. The raw weighted formula includes both
the neutrino and, if probed, the vacancy. The earlier
`WireSchedule.polarity_cost_difference` is the charged-only subtotal.

The neutral slot in `orbit_record_tolls` and `lepton_reference_toll`
is the static vacancy. `neutral_slot_tolls` uses `same_wall_pair`
to check that its active neutrino partner also has electric bit Tolls
1 and 0. The vacancy has no payload. Its electric sector flag is
computed only if the circuit probes that basis slot against the
colour reference. This concerns the relative electric comparison.
A bare vacancy hypercharge flag is zero.

`expectedRecordCost_eq_mean` identifies the exact bit flags with
the two indicator events in `NetCost.expectedCost`. The position
event contains eight slots. The sector event contains twelve for
lepton and either four or three for colour, depending on whether
the vacancy is probed. Unit registration costs follow from
`record_event_counts`, `packet_record_cost` and
`packet_record_difference`.

| Conditional sampling and visit policy | Colour mean | Lepton mean | Colour minus lepton |
| --- | --- | --- | --- |
| Uniform full packet, both comparisons probe the vacancy | 12/16 | 20/16 | −8/16 = −1/2 |
| Uniform full packet, vacant slot is idle | 11/16 | 20/16 | −9/16 |
| Uniform on the fifteen occupied slots | 11/15 | 20/15 | −9/15 = −3/5 |

The proposed `−9` is an unnormalized count when the vacancy
contributes zero. A full-slot probe instead gives `−8` in sum units.
A ledger of one separately required paid read per slot would use
sums by `ReadoutAdditivity.additive_read`. That is a different
execution claim from sampling a single incoming slot per cycle.
The remainder must have the same units as the bit cost.

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

## Marginal cost of the two references

These are separate stages in a candidate writer trace. A flag
contributes registrations only if that comparison is paid. An
exchange that both restores the live slot and displaces the record
is one event. Later record shifts have their own price.

| Stage | Colour-reference account | Lepton-reference account |
| --- | --- | --- |
| Seed loading and bank preparation | A supplied first-wall odd rest seed gives one unit of incoming reference population per visit (`OddReferenceSource.odd_seed_train_restores`). The companion setup gives active and static flag sums 1/2 and 3/4, with mean 5/8 at equal wall weights (`ElectricCompanionSetupToll.primitive_setup_sum`, `equal_slot_setup_sum`). | The same conditional budgets apply if this writer uses that seed and setup. Seed supply, loading admission, visits and which flags are paid remain open for both references. Population is a supply requirement. The inverse decoder's preparation instead gives one flag on its supplied seed (`ElectricPrimitiveToll.preparation_flags`). |
| Writer pulse control | The exhibited two-bit root writer has factor budget `1 + T_colour/2` per visited input (`ElectricHeavyRecord.pulse_flags`, `two_bit_factor_toll`). | The complemented sector flag gives `1 + T_lepton/2` under the same writer contract (`WireReferenceCost.factorFlagToll_eq`). Use the factor ledger in place of the output-bit ledger. Joint coupling, scheduling and physical pricing of the visits remain open. |
| Primitive decoder and current alternatives | `ElectricPrimitiveToll.primitive_decoder_flags` and `forward_tolls` account for the alternate short decoder. `ElectricChiralKick.swapped_exposure_toll` and `total_tolls` include its current kicks and intervening swap. | These are other writer circuits. They supply no marginal polarity price for the two-bit word. Both references still need a physical pulse tariff and actual allocation of the selected program. |
| Export | `OpenHandoff.export_trace` puts one displaced live value from each exchange in a distinct downstream record slot. `sum_exported` gives the same sum of populations at the export slots as on those incoming live states. | The same identity holds for lepton and any supplied record train. KAutomaton of unit-population inputs thus reserves one unit per routed value. It does not price the shift or identify the two-bit record with one or two open routes. Those encodings, visits and tariffs remain open. |
| Reset and reuse | `OpenHandoff.balanced_basis_repair_flag` gives a flag of 0 for a clean zero and 1/2 for an orthogonal written one, with equal input populations and a fresh zero. It includes a unit phase on the marked port. | The same swap would price each independently encoded and separately paid bit at half its output flag for lepton. This would add `T_ref/2` for two such resets for either reference. The actual writer-to-receiver encoding, reference renewal, any inverse uncompute and any later reuse tariff remain open. |
| Maintenance sharing | With L in the reserved cell, the colour refresh's reference sits in the payload (`ColourReference.colour_reference_in_payload`). Its twelve payload obligations have cost `12η` in the baseline allocation model (`colour_ledger_minimal`). | `SharedReference.shared` gives one reserved type for weak and hypercharge. `ReferenceEconomy.economy_selects_lepton` picks L under colour preservation and its allocation model. `reads_reserved` treats the reserved cell as paid. This is baseline sharing. Neither reference has a proof that the heavy writer uses the same paid jobs at its required state and time. |

The closed exchange returns in four steps (`exchange_four_returns`).
Four uninterrupted exact restorations require every initial slot to
hold the reference (`four_restorations_iff`). On a ring the
disturbance returns (`RecordSupply.ring_returns`). An open translated
route restores indefinitely with the supplied references
(`lattice_forever`). `CoherentRecordRestoration.prepared_repair`
retains the input in the record. `twice_undoes` rules out treating
that occupied record as another fresh reference. Its
`unitary_reset_factorization` forces a retained encoding for the
stated linear reset. The companion update returns ready only at
the active neutral port (`written_port_ready_iff`). Universal
closed cleaning of the heavy record is excluded
(`HeavyFlipNativeBoundary.no_closed_cleaning`). None of these
results supplies new ready references or prices a renewal trace.

The marginal upkeep is the sum over writer jobs absent from the
baseline (`WireReferenceCost.added_maintenance_eq`). If either writer
uses only baseline jobs at the required state and time, that
writer adds zero upkeep (`shared_maintenance_free`). A shared cell
or a payload reference proves no such job inclusion.
`ElectricHeavyRecord.sectorDifference` fixes a charge subtraction
and supplies no resource address or restoration rule. The
`12η` allocation ledger gives no bound in registrations per writer
input. Common preparation or exports cancel only after checking
the same work and tariff for both references.

## Record reference remains undetermined

Let `G` be the colour-minus-lepton difference in the output-bit
account. `reference_threshold` selects colour when `G + ΔR < 0`,
ties at zero and selects lepton when it is positive. Both traces
must be admitted and both costs must use the same units.
`ElectricHeavyRecord.reference_flags_from_orbit_bits` shows that
the two references share the position flag and complement only
the electric sector flag. The receiver duality test supplies
no common choice of polarity for these two mechanisms.

The proved supply and transport identities give no unconditional
registration term in `ΔR`. A common companion bank and export train
could cancel, provided the physical visits and tariff agree. The
balanced two-port circuit also gives a conditional refinement.
If both writers use two independently encoded bits and the
separate fresh-zero receiver comparison is paid for each, the
reset difference is `G/2`. This charges the restoring exchange
once, including its displacement of the old record. Further travel,
supply and maintenance enter the remainder `U`. Under that extra
premise the output-bit ledger has `ΔR = G/2 + U`.

The reset term here prices a separate balanced receiver comparison.
Boundary erasure counts booked exports actually reset after their
last use. The flag certificate supplies no writer export itinerary.
`WireReferenceCost.reference_threshold_with_erasure` gives the
replacement threshold `B − (E_C − E_L)`, with output flag threshold
`B` and booked erase counts per input `E_C` and `E_L`. Equal erase
counts leave `B`. The tagged receiver train does not supply the
difference between the two writer counts. See the
[boundary stopping point](../PMKAutomaton/TODO.md#admission-and-ports).

| Common sampling policy | Output-bit gap `G` | Conditional reset contribution to `ΔR` | Colour wins with output flags and those resets if |
| --- | ---: | ---: | ---: |
| Uniform full packet, vacancy probed | −1/2 | −1/4 | `U < 3/4` |
| Uniform full packet, vacancy idle | −9/16 | −9/32 | `U < 27/32` |
| Uniform occupied inputs | −3/5 | −3/10 | `U < 9/10` |

Without that reset premise the output-bit thresholds for the full
`ΔR` remain 1/2, 9/16 and 3/5, respectively
(`packet_record_difference`). `PMKAutomaton.Values` gives both sets of
thresholds. The packet identities are `packet_record_difference_eq_values`
and `balanced_reset_gap_eq_values`. For any common booked population,
`booked_balanced_reset_difference` gives
`U + (3/2)(M_colourless − M_coloured)` under the separate balanced
resets. See KAutomaton's
[Admission](../PMKAutomaton/TODO.md#admission-and-ports) and
[Registration tariff](../PMKAutomaton/TODO.md#clock-and-accounting).
The factor-pulse ledger by itself
has gap `G/2` (`factor_flag_difference`). If the two reset
comparisons are additionally paid and distinct from the writer
factors, factor plus reset gives gap `G`. None of these conditionals
admits a native reset, rules out a different encoding, or prices
the rest of the record route.

For the comparison, the smallest missing input is an admitted
writer trace for each reference supplying two quantities.

- The **bit or factor gap** for the actual visits. For a common
  visit law, the output-bit gap only needs the difference between
  the booked colourless and coloured input masses
  (`booked_population_difference`). An idle vacancy contributes
  neither mass. If the two writers admit different traffic, their
  two expected charges replace this common-population formula.
- The **signed difference in remaining paid work** after common
  jobs cancel, including which resets or uncomputations actually
  run. This needs the timed supply, polarity control,
  export, renewal and maintenance jobs and their tariffs only
  where they differ. It is enough to bound this difference on one
  side of the selection threshold.

The clock, route and comparison results leave both quantities open.
The colour ordering and the down geometric mean remain properties
of the colour record at a common bit price. The lepton candidate
still gives `s_d < s_e = s_u`.


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

These are the conditional [clock bounds](../PMKAutomaton/OVERVIEW.md#clock).
They assume one gapped word and one beta word on each beta-driven wall.
A separate class-changing crossing adds twelve quarter-times. The
logical record counts agree for electron, up and down in this template.
The record Tolls differ, and give no elapsed ticks without a control
clock. Neither equality nor inequality of the full period counts across
protocols follows at a physical minimum.

## Comparison only

Use the e8p comparisons for measured references. The geometric mean,
the declared tier ratios and the sensitivity to `r` are separate
checks. No comparison identifies the writer, its tariff or the
physical `r`.
-/

namespace PMElementaryParticles.WireSchedule

/-- At most one occurrence of each block in this serial template. -/
inductive Event
  | staticFlip | gappedCrossing | referenceFlip | gluedCrossing
  | nodeEnter | nodeLeave | referenceRenewal
  | doublet | chargedCurrent | bankSetup | position | sector | recordExport
  | matchFirst | matchSecond | offset | vacancyProbe
  deriving DecidableEq

instance : Fintype Event :=
  Fintype.ofList [.staticFlip, .gappedCrossing, .referenceFlip, .gluedCrossing,
    .nodeEnter, .nodeLeave, .referenceRenewal, .doublet, .chargedCurrent,
    .bankSetup, .position, .sector, .recordExport, .matchFirst, .matchSecond,
    .offset, .vacancyProbe] (by intro e; cases e <;> simp)

 /-- Whole carrier word, retained plus port, minus port, or stored record. -/
inductive Branch
  | carrier | plus | minus | recorded
  deriving DecidableEq

instance : Fintype Branch :=
  Fintype.ofList [.carrier, .plus, .minus, .recorded] (by intro b; cases b <;> simp)

/-- Start, live branch and whether this visit is charged as a registration. -/
abbrev Placement (ticks : ℕ) := Fin ticks × Branch × Bool

/-- The first bit chooses the colour (true) or lepton (false) sector reference. -/
abbrev Schedule (ticks : ℕ) := Bool × (Event → Option (Placement ticks))

/-- All calibration and physical admission choices for this template.
T supplies `quarterTicks`, `shortFlip` and `otherTicks`. G, L, O, U, W, Q
and J supply the admitted joint trace. The horizon is `ticks`. The
admission predicate supplies phase availability,
record lifecycle, ownership of paid visits, and any further trigger constraints.
A fresh record in this template needs its writer in the same cycle. -/
structure Premises (ticks : ℕ) where
  address : Fin 3
  shortFlip : Bool
  quarterTicks : ℕ
  chargedCurrent : Bool
  otherTicks : Event → ℕ
  admits : Schedule ticks → Bool

/-- Flip budgets from the two certified beta words. The crossing budgets
assume serial principal half-pulses on their common root clock. -/
def duration {ticks : ℕ} (p : Premises ticks) : Event → ℕ
  | .staticFlip | .referenceFlip => (if p.shortFlip then 24 else 32) * p.quarterTicks
  | .gappedCrossing | .gluedCrossing => 12 * p.quarterTicks
  | e => p.otherTicks e

/-- Required work in the specified template. The route is from
`ReferenceClassHop` and `ReferenceNode`. The optional charged-current event
needs its position bit (`EventRequirements.pairs_of_sign`). The fresh heavy
record uses both electric visits. The offset uses the two matched tests at
address two (`ChargedInsertion.joint_selector`, `select_static`). -/
def required {ticks : ℕ} (p : Premises ticks) : Event → Bool
  | .staticFlip | .gappedCrossing => true
  | .referenceFlip | .position | .sector => p.address == 0
  | .nodeEnter | .nodeLeave => p.address != 0
  | .doublet | .chargedCurrent => p.chargedCurrent
  | .matchFirst | .matchSecond | .offset => p.address == 2
  | _ => false

/-- [Premise] These are circuit ports in the specified implementation. The heavy
flip's identification with a record-controlled insertion is a premise.
The doublet comparison writes a bit whose two values may both be used,
so its control port is represented by the stored record. -/
def branchAllowed : Event → Branch → Bool
  | .staticFlip, .carrier | .gappedCrossing, .carrier => true
  | .referenceFlip, .recorded | .gluedCrossing, .recorded => true
  | .position, .recorded | .sector, .recorded => true
  | .doublet, .recorded | .chargedCurrent, .recorded => true
  | .matchFirst, .plus | .matchSecond, .plus | .offset, .recorded => true
  | .nodeEnter, _ | .nodeLeave, _ | .referenceRenewal, _ => true
  | .bankSetup, _ | .recordExport, _ | .vacancyProbe, _ => true
  | _, _ => false

/-- Prerequisites of each present event. The static/crossing/reference
chronology is the literal Schur-order premise. The fresh heavy writer
uses the position result to choose the sector reference. -/
def predecessors : Event → List Event
  | .gappedCrossing => [.staticFlip]
  | .referenceFlip => [.gappedCrossing, .sector]
  | .gluedCrossing => [.sector]
  | .nodeEnter => [.gappedCrossing]
  | .nodeLeave => [.nodeEnter]
  | .chargedCurrent => [.doublet]
  | .sector => [.position]
  | .matchSecond => [.matchFirst]
  | .offset => [.matchSecond]
  | _ => []

def endsBefore {ticks : ℕ} (p : Premises ticks) (s : Schedule ticks) (a b : Event) : Bool :=
  match s.2 a, s.2 b with
  | some x, some y => decide (x.1.val + duration p a ≤ y.1.val)
  | _, _ => false

/-- Optional events may be omitted on their route but cannot use the wrong address. -/
def allowed {ticks : ℕ} (p : Premises ticks) : Event → Bool
  | .gluedCrossing | .bankSetup | .recordExport => p.address == 0
  | .referenceRenewal | .vacancyProbe => true
  | e => required p e

private def fitsEvent {ticks : ℕ} (p : Premises ticks) (s : Schedule ticks)
    (e : Event) : Bool :=
  match s.2 e with
  | none => !required p e
  | some x =>
      allowed p e &&
      decide (0 < duration p e ∧ x.1.val + duration p e ≤ ticks) &&
      branchAllowed e x.2.1 &&
      (predecessors e).all (fun a => endsBefore p s a e) &&
      (e != .position || !(s.2 .bankSetup).isSome || endsBefore p s .bankSetup e) &&
      (e != .recordExport || [.referenceFlip, .gluedCrossing].all
        (fun a => !(s.2 a).isSome || endsBefore p s a e)) &&
      decide (∀ f : Event,
        (e == f || !(s.2 f).isSome || endsBefore p s e f || endsBefore p s f e) = true)

/-- Test the finite constraints. Optional setup precedes the writer if
present. Export is timed after every present consumer of the heavy record.
The admission premise checks that an omitted setup or export is viable. -/
def admissible {ticks : ℕ} (p : Premises ticks) (s : Schedule ticks) : Bool :=
  p.admits s &&
    decide (0 < p.quarterTicks) &&
    (p.shortFlip || p.quarterTicks % 2 == 0) &&
    decide (∀ e : Event, fitsEvent p s e = true)

/-- Computably enumerable for a supplied finite horizon and Boolean admission
test. Costs can be minimized on projections without iterating slot injections. -/
def family {ticks : ℕ} (p : Premises ticks) : Finset (Schedule ticks) :=
  Finset.univ.filter (fun s => admissible p s = true)

theorem mem_family {ticks : ℕ} (p : Premises ticks) (s : Schedule ticks) :
    s ∈ family p ↔ admissible p s = true := by
  simp [family]

/-- Convert a start tick to a period and a phase, from the supplied clock origin. -/
def periodPhase {ticks : ℕ} (start : Fin ticks) : ℕ × ℕ :=
  (start.val / PMSubstrate.E8Values.Delta, start.val % PMSubstrate.E8Values.Delta)

/-- Last exclusive end of a booked block, measured from the clock origin. -/
def finishTick {ticks : ℕ} (p : Premises ticks) (s : Schedule ticks) : ℕ :=
  Finset.univ.sup fun e =>
    match s.2 e with
    | none => 0
    | some x => x.1.val + duration p e

def periods {ticks : ℕ} (p : Premises ticks) (s : Schedule ticks) : ℕ :=
  (finishTick p s + PMSubstrate.E8Values.Delta - 1) / PMSubstrate.E8Values.Delta

theorem finishTick_le_horizon {ticks : ℕ} (p : Premises ticks) (s : Schedule ticks)
    (hs : s ∈ family p) : finishTick p s ≤ ticks := by
  have h := (mem_family p s).1 hs
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at h
  have hall : ∀ e : Event, fitsEvent p s e = true := by tauto
  apply Finset.sup_le
  intro e _
  have he := hall e
  cases hplace : s.2 e with
  | none => simp
  | some x =>
    simp only [fitsEvent, hplace, Bool.and_eq_true, decide_eq_true_eq] at he
    tauto

/-- Required events have an actual placement with positive duration, an
allowed branch and the stated earlier visits. Physical admission remains
the supplied predicate of the schedule. -/
theorem required_placement {ticks : ℕ} {p : Premises ticks} {s : Schedule ticks}
    (hs : s ∈ family p) {e : Event} (he : required p e = true) :
    ∃ x, s.2 e = some x ∧ 0 < duration p e ∧ branchAllowed e x.2.1 = true ∧
      ∀ f ∈ predecessors e, endsBefore p s f e = true := by
  have h := (mem_family p s).1 hs
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at h
  have hall : ∀ e : Event, fitsEvent p s e = true := by tauto
  have hx := hall e
  cases hp : s.2 e with
  | none => simp [fitsEvent, hp, he] at hx
  | some x =>
    refine ⟨x, rfl, ?_⟩
    simp only [fitsEvent, hp, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at hx
    tauto

/-- The exclusive finish of a placed event is bounded by the schedule finish. -/
theorem placement_le_finish {ticks : ℕ} (p : Premises ticks) (s : Schedule ticks)
    {e : Event} {x : Placement ticks} (hx : s.2 e = some x) :
    x.1.val + duration p e ≤ finishTick p s := by
  have h := Finset.le_sup (s := Finset.univ) (f := fun e =>
    match s.2 e with
    | none => 0
    | some x => x.1.val + duration p e) (Finset.mem_univ e)
  rw [hx] at h
  exact h

/-- The sum of the three booked durations is a lower bound for the elapsed
time when the visits are in succession. Waiting may make the elapsed time
larger. -/
theorem serial_three_le_finish {ticks : ℕ} (p : Premises ticks) (s : Schedule ticks)
    {a b c : Event} {x y z : Placement ticks}
    (hx : s.2 a = some x) (hy : s.2 b = some y) (hz : s.2 c = some z)
    (hab : endsBefore p s a b = true) (hbc : endsBefore p s b c = true) :
    duration p a + duration p b + duration p c ≤ finishTick p s := by
  have hLast := placement_le_finish p s hz
  simp only [endsBefore, hx, hy, decide_eq_true_eq] at hab
  simp only [endsBefore, hy, hz, decide_eq_true_eq] at hbc
  omega

noncomputable section
open PMConstants.PacketGaugeActions ProtocolInventory ProtocolToll
open PMAction DiagonalReadout InterferenceReadout TollAmplitude
open scoped BigOperators

/-- One account for each actual static label, with the opposite wall's
equal population when the visit reads a massive state. The two prep flags
are available only for the certified equal-slot companion setup. -/
def visitFlag (companionSetup colourReference : Bool) (c : Channels) : Event → Option ℝ
  | .position => some (flag (3 * Real.pi * ElectricHeavyRecord.q c))
  | .sector => some (flag (3 * Real.pi / 2 * ElectricHeavyRecord.sectorDifference colourReference c))
  | .doublet => some (EventRequirements.massiveFlag (3 * Real.pi / 2)
      (ControlledGluedRegister.opposite c) c)
  | .matchFirst => some (flagProbability (ChargedInsertion.matchedTransport (baseProtocol c)) c)
  | .matchSecond =>
      let U := ChargedInsertion.matchedTransport (baseProtocol c)
      some (flagProbability (U * U) c)
  | .vacancyProbe => some (hyperchargeFlag (3 * Real.pi / 4) c)
  | .bankSetup =>
      if companionSetup then some (((∑ j, ElectricCompanionSetupToll.visitFlag true j) +
        ∑ j, ElectricCompanionSetupToll.visitFlag false j) / 2) else none
  | _ => none

def paid {ticks : ℕ} (s : Schedule ticks) (e : Event) : Bool :=
  ((s.2 e).map (fun x => x.2.2)).getD false

/-- This is a subtotal. A visit with no proved flag contributes only to the
unpriced part of the account, even if the schedule marks it as paid. -/
def knownToll {ticks : ℕ} (companionSetup : Bool) (c : Channels) (s : Schedule ticks) : ℝ :=
  ∑ e, if paid s e then (visitFlag companionSetup s.1 c e).getD 0 else 0

def unpricedVisits {ticks : ℕ} (companionSetup : Bool) (c : Channels)
    (s : Schedule ticks) : Finset Event :=
  Finset.univ.filter (fun e => paid s e = true ∧ (visitFlag companionSetup s.1 c e).isNone = true)

/-- The explicit remainder pays the unpriced visits and any additional
preparation, primitive pulse, export, renewal and controller costs.
It must be supplied by a physical account. -/
def fullToll {ticks : ℕ} (companionSetup : Bool) (unpriced : Channels → Schedule ticks → ℝ)
    (c : Channels) (s : Schedule ticks) : ℝ :=
  knownToll companionSetup c s + unpriced c s

def amplitude {ticks : ℕ} (companionSetup : Bool) (unpriced : Channels → Schedule ticks → ℝ)
    (c : Channels) (s : Schedule ticks) : ℝ :=
  PersistenceMechanics.EffectiveAction.attenuationWeight 1 (fullToll companionSetup unpriced c s)

theorem matched_flag_account (b pol : Bool) (c : Channels) (hc : active c = false) :
    visitFlag b pol c .matchFirst = some 0 ∧ visitFlag b pol c .matchSecond = some 0 := by
  obtain ⟨h₁, h₂⟩ := ChargedInsertion.matched_flags_zero (baseProtocol c) c hc rfl
  exact ⟨congrArg some h₁, congrArg some h₂⟩

theorem knownToll_eq_of_paid_eq {ticks : ℕ} (b : Bool) (c : Channels)
    {s t : Schedule ticks} (hp : s.1 = t.1) (h : ∀ e, paid s e = paid t e) :
    knownToll b c s = knownToll b c t := by
  simp [knownToll, hp, h]

end

noncomputable section
open PMConstants.PacketGaugeActions ProtocolToll
open PMAction DiagonalReadout TollAmplitude

/-- Exact minima once the physical scalar cost is supplied. -/
def minima {ticks : ℕ} (p : Premises ticks) (cost : Schedule ticks → ℝ) :
    Finset (Schedule ticks) := by
  classical
  exact (family p).filter (fun s => ∀ t ∈ family p, cost s ≤ cost t)

theorem mem_minima {ticks : ℕ} (p : Premises ticks) (cost : Schedule ticks → ℝ)
    (s : Schedule ticks) :
    s ∈ minima p cost ↔ s ∈ family p ∧ ∀ t ∈ family p, cost s ≤ cost t := by
  classical
  simp [minima]

theorem minima_nonempty {ticks : ℕ} (p : Premises ticks) (cost : Schedule ticks → ℝ)
    (h : (family p).Nonempty) : (minima p cost).Nonempty := by
  obtain ⟨s, hs, hmin⟩ := (family p).exists_min_image cost h
  exact ⟨s, (mem_minima p cost s).2 ⟨hs, hmin⟩⟩

/-- Economy picks precisely the maximal survival schedules inside the supplied family. -/
theorem best_survival_iff {ticks : ℕ} (p : Premises ticks) (cost : Schedule ticks → ℝ)
    (s : Schedule ticks) (β baseline : ℝ) (hβ : 0 < β) :
    (s ∈ family p ∧ ∀ t ∈ family p,
      Real.exp (-β * (baseline + cost t)) ≤ Real.exp (-β * (baseline + cost s))) ↔
      s ∈ minima p cost := by
  rw [mem_minima]
  exact PersistenceSelection.within_family_iff_cheapest β hβ cost (↑(family p)) baseline s

theorem tied_minimum {ticks : ℕ} (p : Premises ticks) (cost : Schedule ticks → ℝ)
    {s t : Schedule ticks} (hs : s ∈ minima p cost) (ht : t ∈ family p)
    (heq : cost t = cost s) : t ∈ minima p cost := by
  exact (mem_minima p cost t).2 ⟨ht, fun u hu =>
    heq.trans_le (((mem_minima p cost s).1 hs).2 u hu)⟩

/-- The observable two-visit subtotal when both electric record flags are paid. -/
def bitToll (colourReference : Bool) (c : Channels) : ℝ :=
  flag (3 * Real.pi * ElectricHeavyRecord.q c) +
    flag (3 * Real.pi / 2 * ElectricHeavyRecord.sectorDifference colourReference c)

/-- In the record-only account, the finite sum is exactly the two write flags. -/
theorem knownToll_recordOnly {ticks : ℕ} (b : Bool) (c : Channels) (s : Schedule ticks)
    (hp : paid s .position = true) (hs : paid s .sector = true)
    (ho : ∀ e, e ≠ .position → e ≠ .sector → paid s e = false) :
    knownToll b c s = bitToll s.1 c := by
  classical
  unfold knownToll bitToll
  rw [← Finset.sum_subset (Finset.subset_univ ({.position, .sector} : Finset Event)) ?_]
  · rw [Finset.sum_pair (show Event.position ≠ Event.sector by decide)]
    simp [hp, hs, visitFlag]
  · intro e _ he
    have h : e ≠ Event.position ∧ e ≠ Event.sector := by simpa using he
    simp [ho e h.1 h.2]

theorem colour_tolls (a : Fin 3) :
    bitToll true electronStatic = 2 ∧ bitToll true (upStatic a) = 0 ∧
      bitToll true (downStatic a) = 1 := by
  obtain ⟨he, hd, hu, -⟩ := HeavyFlipRecords.orbit_record_tolls a
  simpa only [bitToll, ElectricHeavyRecord.colour_reference_toll] using
    (show HeavyFlipRecords.orbitRecordToll electronStatic = 2 ∧
        HeavyFlipRecords.orbitRecordToll (upStatic a) = 0 ∧
        HeavyFlipRecords.orbitRecordToll (downStatic a) = 1 from ⟨he, hu, hd⟩)

theorem lepton_tolls (a : Fin 3) :
    bitToll false electronStatic = 1 ∧ bitToll false (upStatic a) = 1 ∧
      bitToll false (downStatic a) = 2 := by
  obtain ⟨he, hd, hu, -⟩ := ElectricHeavyRecord.lepton_reference_toll a
  exact ⟨he, hu, hd⟩

/-- Neither polarity weakly improves the known cost for every charged label. -/
theorem polarity_tradeoff (a : Fin 3) :
    bitToll false electronStatic < bitToll true electronStatic ∧
      bitToll true (upStatic a) < bitToll false (upStatic a) ∧
      bitToll true (downStatic a) < bitToll false (downStatic a) := by
  obtain ⟨he, hu, hd⟩ := colour_tolls a
  obtain ⟨he', hu', hd'⟩ := lepton_tolls a
  rw [he, hu, hd, he', hu', hd']
  norm_num

/-- For a common schedule, weights on the three charged labels must be supplied.
The remainder here includes all other contributions to the scalar objective. -/
def polarityCost (a : Fin 3) (we wu wd : ℝ) (remainder : Bool → ℝ) (pol : Bool) : ℝ :=
  we * bitToll pol electronStatic + wu * bitToll pol (upStatic a) +
    wd * bitToll pol (downStatic a) + remainder pol

/-- Exact threshold when the only candidates differ by sector-reference polarity
and the two output flags are charged in both. -/
theorem polarity_cost_difference (a : Fin 3) (we wu wd : ℝ) (remainder : Bool → ℝ) :
    polarityCost a we wu wd remainder true - polarityCost a we wu wd remainder false =
      we - wu - wd + (remainder true - remainder false) := by
  obtain ⟨he, hu, hd⟩ := colour_tolls a
  obtain ⟨he', hu', hd'⟩ := lepton_tolls a
  simp only [polarityCost, he, hu, hd, he', hu', hd']
  ring

theorem polarity_minimum_iff (a : Fin 3) (we wu wd : ℝ) (remainder : Bool → ℝ) :
    (∀ pol, polarityCost a we wu wd remainder true ≤ polarityCost a we wu wd remainder pol) ↔
      we - wu - wd + (remainder true - remainder false) ≤ 0 := by
  rw [← polarity_cost_difference, sub_nonpos]
  constructor
  · exact fun h => h false
  · intro h pol
    cases pol
    · exact h
    · exact le_rfl

theorem polarity_tie_iff (a : Fin 3) (we wu wd : ℝ) (remainder : Bool → ℝ) :
    polarityCost a we wu wd remainder true = polarityCost a we wu wd remainder false ↔
      we - wu - wd + (remainder true - remainder false) = 0 := by
  rw [← polarity_cost_difference, sub_eq_zero]

end

end PMElementaryParticles.WireSchedule
