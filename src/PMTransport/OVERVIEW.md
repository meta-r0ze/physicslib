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
| Exchange or pass through a node | `OpenReferenceFlow`, `HandoffAdmittance`, `ReferenceClassHop` | Exact exchange and bypass destinations. Stationarity of a class-definite reference constrains direct class exchange on its wall. |
| Hold, export, and renew a record | `IndependentRegisters`, `RegisterControl`, `ReferenceMaintenance`, `RecordSupply`, `HomogeneousRouting` | Reversible register banks, exact restoration, and export of the previous state. An open backward orbit allows sustained renewal under the supplied reference conditions. |
| Compare and count | `BranchPulseContract`, `RefreshSchedule`, `CoherentRefresh`, `CoherentGate` | Coherent comparison under the pulse contract, orthogonal records for overlapping outputs, and minimum additive cost for required visits at supplied prices. |
| Schedule native operations | `ClockPeriod`, `ClockDynamics`, `ClockControlledRoot`, `RootTransferPhase` | The substrate period, reversible clocked words, and root pulse areas. Physical phase admission and absolute timing remain open. |

The [machine overview](Machine/OVERVIEW.md) lists the supporting carrier,
register, reference, and clock constructions.

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
