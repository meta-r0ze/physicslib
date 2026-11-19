# PMTransport — checked transport results

PMTransport connects the E8 carrier operations to state and record transfer at a
node. A transport can combine a spatial hop, an internal glue-class crossing,
and a comparison with a reference. Each has its own input, output, and event
count. Particle applications specify which payload and record participate.

## Module map

| Task | Entry points | Checked result |
| --- | --- | --- |
| Route between sites | `NativeCarrierProtocol`, `NativePacketRouting`, `NativePacketUpdate` | Reversible port routing, exact carrier readout, and locality under the stated routing realization. |
| Change glue class | `GluedRegister`, `CarrierTriality` | The six-root crossing realizes swap and diagonal triality on glued roots. Triality on a diagonal glued carrier relabels the odd amplitudes by the matrix `M/2`. |
| Exchange or pass through a node | `TwoSiteHandoff`, `OpenReferenceFlow`, `HandoffAdmittance`, `ReferenceClassHop` | Exact exchange and bypass destinations. Stationarity of a class-definite reference constrains direct class exchange on its wall. |
| Hold, export, and renew a record | `IndependentRegisters`, `RegisterControl`, `ReferenceMaintenance`, `RecordSupply`, `HomogeneousRouting` | Reversible register banks, exact restoration, and export of the previous state. An open backward orbit allows sustained renewal under the supplied reference conditions. |
| Compare and count | `BranchPulseContract`, `RefreshSchedule`, `CoherentRefresh`, `CoherentGate` | Coherent comparison under the pulse contract, orthogonal records for overlapping outputs, and minimum additive cost for required visits at supplied prices. |
| Schedule native operations | `ClockPeriod`, `ClockDynamics`, `ClockControlledRoot`, `RootTransferPhase` | The substrate period, reversible clocked words, and root pulse areas. Physical phase admission and absolute timing remain open. |

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
