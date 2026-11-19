# PMTransport — checked transport results

PMTransport connects the E8 carrier operations to state and record transfer at a
node. A transport can combine a spatial hop, an internal glue-class crossing,
and a comparison with a reference. Each has its own input, output, and event
count. Particle applications specify which payload and record participate.

## Module map

The current results give three groups of work. Carrier routing and glue-class
crossing move the carrier. The receiver and record operations restore and retain
state. The clock and the comparison ledger govern and account for those visits.

| Task | Entry points | Checked result |
| --- | --- | --- |
| Route between sites | `NativeCarrierProtocol`, `NativePacketRouting`, `NativePacketUpdate` | Reversible port routing, exact carrier readout, and locality under the stated routing realization. |
| Change glue class | `GluedRegister`, `CarrierTriality` | The six-root crossing realizes swap and diagonal triality on glued roots. Triality on a diagonal glued carrier relabels the odd amplitudes by the matrix `M/2`. |
| Exchange or pass through a node | `TwoSiteHandoff`, `OpenReferenceFlow`, `HandoffAdmittance`, `ReferenceClassHop` | Exact exchange and bypass destinations. Stationarity of a class-definite reference constrains direct class exchange on its wall. |
| Hold, export, and renew a record | `OpenHandoff`, `OddReferenceSource`, `IndependentRegisters`, `RegisterControl`, `ReferenceMaintenance`, `RecordSupply`, `HomogeneousRouting` | Reversible register banks, exact restoration, and export of the previous state. An open backward orbit allows sustained renewal under the supplied reference conditions. |
| Compare and count | `BranchPulseContract`, `RefreshSchedule`, `CoherentRefresh`, `CoherentGate` | Coherent comparison under the pulse contract, orthogonal records for overlapping outputs, and minimum additive cost for required visits at supplied prices. |
| Schedule native operations | `ClockedRootTrials`, `RootClockCalibration`, `ClockPeriod`, `ClockDynamics`, `ClockControlledRoot`, `RootTransferPhase` | The substrate period, reversible clocked words, and root pulse areas. Physical phase admission and absolute timing remain open. |

The [machine overview](Machine/OVERVIEW.md) lists the supporting carrier,
register, reference, and clock constructions.

## Two-site handoff and the six pillars

`TwoSiteHandoff` checks one reversible information-transfer protocol within a
host system. The wire already has a
[six-pillar interpretation](../PMElementaryParticles/README.md#the-six-pillars-on-the-wire).
Here the roles apply to a single handoff and its repeat operation. The
[substrate pillar results](../PMSubstrate/Pillars.lean) give the mechanisms
used to identify those roles.

| Pillar | Role in this handoff |
| --- | --- |
| Capacity | The code has two live and two record carrier modes at each site (`port_count`). A running reference supply still needs a host resource. |
| Map | The receiver exchange restores the live register when the incoming record holds the reference. It retains the other arriving state in the record port (`first_reference_iff`, `step_trace`). |
| Protocol | The edge moves both streams. Bypass keeps their order and exchange uses the actual receiver root. The native matrices realize both branches (`exchange_lookup`, `native_step_observed`). The spatial routing is supplied. |
| Governor | The branch choice and allowed firing phases control which local update executes. An admitted reconstructed root phase realizes the exchange at two root quarter-times (`receiver_half_pulse`). The trigger, physical rate and timing of the hop remain open. |
| Toll | The hop and exchange have exact comparison flags (`hop_flag`, `exchange_flag`). Converting these flags to charged registrations requires a selected comparator and tariff. |
| Margin | A viability margin needs a specified disturbance and ready-reference supply. In the closed pair, four exact restorations require all four initial slots to hold the reference (`four_restorations_iff`). |

### One visit and repeat operation

Write the sender pair as `(live, record)`. One shift delivers that pair to
the receiver and sends the old receiver pair to the sender. Bypass leaves the
arriving pair as it is. The receiver root exchanges it to `(record, live)`.
The following shift carries the receiver's outgoing record to the sender
(`arrivals_observed`, `step_trace`, `export_trace`). This models a closed
pair. The same receiver result holds on the open line when the two values
are supplied by the line's independent arrivals (`receiver_agrees_with_line`).

The second exchange receives its reference from the original receiver's
record slot. Four unconditional exchanges return the entire initial state
(`second_reference_iff`, `exchange_four_returns`). Sustained restoration
against arbitrary disturbances needs a renewal mechanism beyond this closed
edge. The [open reference flow](Machine/OpenReferenceFlow.lean) supplies the
corresponding result under its incoming-reference condition.

For live and record amplitudes `Lₓ` and `Rₓ`, the hop flag is
`(‖L₀−L₁‖² + ‖R₀−R₁‖²)/2`. With exchange, the receiver adds
`‖L₁−R₁‖²/2`. These formulas apply to the specified before-and-after
state comparisons. Read them as probabilities for normalized input.
[TwoSiteHandoff](TwoSiteHandoff.lean)

## Open route and reference supply

`OpenHandoff` embeds the two-stream line into actual D₄ sites along the
primitive root direction `(1,1,0,0)`. Distinct indices give distinct sites,
and consecutive indices differ by one nearest-neighbour root
(`address_injective`, `address_is_site`, `address_step`). The transport
law uses the supplied line shift and receiver exchange.

At visit `k ≥ 1`, the receiver takes its live output from the initial
record at site `+k`. It accepts the initial live value from site `−k`
and retains it as the outgoing record (`receiver_trace`). After `N` visits,
site `−d` for `0 ≤ d < N` holds the displaced live state from site
`d−N` (`export_trace`). Every displaced value therefore has a distinct
record destination. The receiver's comparison flag at each visit is half
the squared amplitude difference between the two corresponding initial
arrivals (`receiver_flag`).

Restoration through `N` visits holds exactly when the first `N` upstream
records hold the required reference. The same equivalence holds for any
specified reference tolerance (`acceptance_iff_supply`). The occupied
input population required for exact restoration is `N‖r‖²`, or one unit
per visit for the existing basis reference (`population_required`,
`basis_population_required`). If the records are loaded by the existing
root preparation, exact restoration requires its known occupied seed at
each loading site (`basis_loading_iff`). Physical selection of the seed
source, admission and timing of the translation and receiver, and the
registration tariff remain open.

### Odd rest modes as occupied reference candidates

A single carrier basis label has a component outside the antipodal-odd
sector. This includes the old basis seed and record of
`RootReferencePreparation`. A parity-preserving control leaves an odd input
in the odd sector. The existing orthogonal-root phase words therefore cannot
supply either basis label from an odd input at any phase times
(`basis_label_not_odd`, `root_phase_word_no_basis`). This exclusion is
independent of the uniform-source tests in
[ReferenceSourceBoundary](Machine/ReferenceSourceBoundary.lean).

`OddReferenceSource` supplies an alternative using an already occupied odd
rest mode. On the first wall, axes 0 and 1 are rest coordinates and the
root in `e₀−e₁` swaps them. On the second wall the corresponding axes
are 2 and 3, with root `e₂−e₃`. Both input and output have unit population
and zero native rest action in all three glue classes. The selected wall
loader is unitary and acts as identity on the other wall
(`rest_stationary`, `rest_population`, `wall_loader_unitary`,
`load_rest_mode`). Each wall has two distinct stationary states of this
form, so stationarity leaves the choice of input axis open
(`rest_modes_distinct`). The reconstructed loading pulse remains in the
rest kernel for its entire evolution (`loading_pulse_stays_at_rest`).

On the vector-class first wall, these two rest axes are the existing
live and record ports with the normalized odd profile proportional to
`(1,−1)`. The open route restores that profile at every visit whose
upstream loader receives the occupied odd seed. It still draws one unit
of input population per visit
(`first_wall_ports`, `odd_seed_train_restores`). The result supplies
a local preparation from an occupied rest state and an exact renewal
contract. Selection and allocation of the occupied input and admission
and timing of the wall loader and the spatial shift remain open.

## Node handoff and admittance

The receiver's exchange and bypass operations put the same incoming bit into
different registers. Exchange sends it back toward its source on the next
tick. Bypass leaves it on the through stream. One maintenance swap converts the
exchanged state into the bypass state. Either update retains the incoming bit.

With independent through weight `w`, the all-pass history has weight `w^n`.
It is the only history that crosses `n` layers in `n` ticks at speed one.
The two-stream current is `w (nR − nL)`, so the conductance in open-channel
units is `w`. With the substrate admittance `α`, this fixes the through
weight of the chosen coherent pulse to `cos² t = α`
(`node_current`, `handoff_from_conductance`, `direct_crossing`).

The one-pass mixture uses relabeling symmetry to transfer the calibration.
A two-pass mixture gives a different interior weight. Uniform carrier sampling
under one reflection only gives multiples of `1/8`. With fixed per-branch costs,
an endpoint minimizes the single-visit expected cost. The coherent pulse
calibration transfers between labels when both experiments use the same
preparation and detector
(`two_pass_alternative`, `reflected_event_ne_alpha`,
`one_tick_cost_endpoint`, `pulse_calibration_transfers`).
The module is [HandoffAdmittance](HandoffAdmittance.lean).

## Calibrating the root clock

A moving root label sees the full complex phase of a reconstructed root
pulse. Two such pulse maps agree exactly when their accumulated gaps
differ by an integer multiple of `2π`. A one-tick alias persists at
every integer tick. Gaps `π` and `3π` both complete a reflection on
the first tick and give the same entire coherent integer-tick history
(`phase_alias_iff`, `integer_samples_agree`, `ambiguous_exchange_clock`).

The statistical transfer supplies a separate observable. On a moved
input label, two trials change the label with weight
`w = (1 − (1−2p)²)/2 = 2p(1−p)`. On the admissible lazy-transfer
interval this fixes the attempt parameter and the gap
`g = −log(1−2w)`. On the prepared vector-class odd live seed, the
same test reads the total probability on the two record-port labels,
so the input can be prepared in the odd sector
(`trial_weight`, `gap_from_trials`, `trial_weight_inj`,
`odd_seed_trial_weight`).

The reconstructed generator uses one time unit for the squared statistical
transfer. In those units an exact reflection after time `N` requires
`−N log(1−2w) = π + 2πk`. For the principal exchange this gives
`w = (1 − exp(−π/N))/2`. A coherent flag also fixes the rate if a separate
argument puts the accumulated gap in `[0,π]`
(`exchange_tick_iff`, `principal_trial_weight`, `principal_flag_inj`).
[RootClockCalibration](RootClockCalibration.lean)

The 43-phase reference excursion has boundaries at phases 0 and 1. A
reversible tick can apply the same E8 root reflection at either boundary
and retains the two request bits. The pair advances the clock to phase 2.
A moved input changes exactly when the two bits differ. Reusing one
request either runs the closed excursion or leaves the carrier idle,
giving zero endpoint-change weight. With equal marginals `p` and joint true-true weight `j`, the
endpoint-change weight is `2(p−j)`. It reproduces the independent-trial
readout exactly when `j = p²`
(`pair_endpoint`, `shared_fire`, `matches_independent_trial_weight`).

When the squared statistical transfer represents these two elapsed
substrate ticks, the generator per tick is `G/2`. The reconstructed
coherent exchange test after `N` substrate ticks is then
`−N log(1−2w)/2 = π + 2πk`.
The principal exchange requires `w = (1 − exp(−2π/N))/2`
(`heat_after_two_ticks`, `phase_in_ticks`, `exchange_in_ticks_iff`,
`principal_weight_in_ticks`).
The physical protocol still needs a source for the joint request law,
a link between this elapsed time and its coherent pulse, and a registration
observable and tariff.
[ClockedRootTrials](ClockedRootTrials.lean)

## Heavy-label application

The particle library uses the native root and current constructions to prepare
the other-wall companion and write its electric record. The companion carries
the class address and the record. Its setup uses one root for the active-wall
seed and two for the static-wall seed. The executed setup has conditional flag
sums of `1/2` and `3/4`. The heavy guard, charged ladder, and mass comparison
remain in the particle application.
[Companion-bank results](../PMElementaryParticles/OVERVIEW.md#triality-preparation-on-the-companion)

## Import and build boundaries

`PMTransport.Machine` and selected PMAction modules share an upstream build layer.
The machine uses PMAction's finite linear algebra and dynamics proofs. PMAction
also uses machine results. The Lean module graph sets the dependency order
inside that layer. The packet-level `PMTransport` target follows PMConstants.
PMAction and PMConstants can import machine modules. Packet transport can import
PMConstants, and Elementary Particles and Flavor can import packet transport.
The [dependency audit](../AuditDependencies.lean) checks those directions.
Existing declaration namespaces remain available under the new import paths.
