# PMKAutomaton — checked results

The results keep their stated hypotheses. Use [TODO](TODO.md) for the open work.
Import `PMKAutomaton.Interface` for transport and `PMKAutomaton.Values` for the checked numbers.

## Clock-timed native cycles

The global phase is native state. `PhaseTimedRing.tick` scatters, streams and
advances it. Each phase uses an admissible site permutation. No external request
sequence is supplied. The following census is complete only for the stated gate
subclass: kind 1 outside S, kind 4 inside S. Both flip the occupied marker.

| Phase symmetry | Proved result | Lean source |
| --- | --- | --- |
| Elements of Gplus whose action descends to the phase reading | Identity only. | `ClockPhaseSymmetry.positive_image` |
| Elements of Gpm whose action descends | Identity and phase negation. | `ClockPhaseSymmetry.full_image` |
| Whole root stabilizer | Does not descend. Its scalar invariance forces a phase-only function to be constant. | `swap_has_no_phase_action`, `full_root_invariance_constant` |
| Negation-invariant gates | Unions of {0} and the 21 pairs {j,43-j}; 22 orbits, every size 0..43. The unique invariant singleton is {0}. | `phase_orbits_card`, `all_invariant_sizes`, `invariant_singleton` |
| Reversal of an ordered scatter/stream tick | The collision-dressed stream exchange at negated phase reverses the tick for inverse-paired tables. Bare phase negation does not commute with phase advance. | `PhaseTimedRing.reverse_involutive`, `reverse_tick`, `negation_does_not_commute_with_advance` |

Nonconstant gates need admission of the retained clock reference. They are not
proved invariant under the whole root stabilizer. This is an open physical bridge.
The reversing map includes the native collision chart; bare stream exchange alone
is not asserted to reverse the ordered tick.

| Gate family | Full-state cycle (ticks); reversals | Average per 43 | Displacement and support | Robustness |
| --- | --- | --- | --- | --- |
| S={0}, n=43 | 86; 2 | 1 | Zero drift; unwrapped displacement stays within 43 of the start. | All markers, positions, directions and phase starts; `ClockGatedCycle.unit_cycle`, `localization_bound`, `marker_phase_robust`. |
| S={0}, odd n=3..13 | 172; 4 | 1 | Zero drift; visited core is n sites. | Same routing independence; computational census. |
| Odd gate count M | 86 if n divides D, otherwise 172; (T/43)M | M | Zero drift; visited core min(n, range+1). | All marker/phase starts; computational census. |
| Even gate count M | 86q; 2qM, q=n/gcd(n,abs(D)) | M | Nonzero drift 2qD, including massless M=0 mover; visits n sites. | All marker/phase starts; computational census. |

Here D is signed displacement during the first 43 updates from phase zero and
forward direction. Opposite direction negates D. The range is that first path's
spatial range. `tools/phase_gate_census.cpp` enumerates all 2^22 invariant S at
n=3,5,7,9,11,13,43. It computes 2,273 grouped rows. These cycle formulas and the
complete subclass census are computation; the n=43 singleton result is proved in
Lean. They do not classify arbitrary phase-dependent marker rules. Support includes
spectator markers if present. Marker-rate robustness is not a proof of recovery of
a labelled excitation, physical Margin, or a unique least rule in the full space.

## Collision-only binding boundary

| Question | Result | Lean source |
| --- | --- | --- |
| What differs at double occupancy? | Both variants output both ports occupied; only the marker differs. | `CollisionBoundary.double_variants_only_marker` |
| How many named packets turn there? | Not encoded: two reversible labelled lifts give the same Boolean successor but 0 or 2 turns. | `lifts_same_native_rule`, `collision_lift_counts`, `no_native_collision_turn_readout` |
| Can turns occur only at collisions and bind the occupation pattern? | No. Conservation plus passing single occupancy forces free stream ports. Every occupied stream escapes any fixed interval on the infinite cover, even for phase-dependent rules. | `collision_only_ports_identity`, `no_confined_collision_only` |
| Can three packets at least have zero total drift without isolated turns? | No; their current is odd and nonzero. | `three_packet_current_nonzero`, `three_packets_not_at_rest` |

| Packets | Label content | Localized collision-only bound state | Period / turns | Robust? |
| --- | --- | --- | --- | --- |
| 2 | AA, AB, BB | None on the infinite cover. Opposite streams can have zero total current on a finite ring. | No bound-state cycle. Named turns need routing. | No such state. |
| 3 | AAA, AAB, ABB, BBB | None; odd current also excludes rest. | No bound-state cycle. Named turns need routing. | No such state. |

The exclusion holds for all ring sizes when localization is tested on the infinite
cover, and for any phase sequence. `CollisionOnlyAlong` requires passing only at
isolated inputs actually encountered, not at every possible input of the rule. Relabelling the same
free occupation flow does not change this conclusion. General marker-mediated
2/3-packet families are not classified here. Their requested per-packet mass census
needs a native routing/action definition; the Boolean variants do not supply it.

## Autonomous native cycle census

`AutonomousRing` has 10 admissible eight-state site rules. `AutonomousCensus` uses
full stream/marker return and average `Delta*R/T`. The earlier one-reversal-per-return
predicate is now named `OneReversalCycle`; its parity no-go does not exclude this test.
The incoming/output port charts are conjugate. Reflection is the existing central
negation element in Gpm, not an action of every Gpm element or inverse-time conjugacy.

Each kind has two double-occupancy marker options. They coincide on one packet
(`double_flip_unseen`). Empty-site markers stay fixed. Finite data cover ALL positions,
directions and marker words at odd n=3..13 via `tools/autonomous_ring_census.py`.
These exhaustive computations are not kernel-certified cycle covers. General rate and
return proofs, and the concrete 43-site witness, are separate Lean results.

| Kind / rules | Family | Native period T; R | Average per 43 | Lifted displacement | Marker-rate robust? |
| --- | --- | --- | --- | --- | --- |
| 0 / both options | No marker; circulating packet | n; 0 | 0 | ±n | No |
| 0 / both | Adjacent reflecting boundaries distance d; no internal reflector | 2d; 2, 1≤d<n | 43/d | 0 | No: remove a boundary. Finite census; general gap classification not yet a Lean theorem. |
| 0 / both | Single mirror | 2n; 2 | 43/n | 0 | No; at n=43 kernel-certified by `mirror43_not_robust`. |
| 1 / both | Pass and flip marker; circulating | 2n; 0 | 0 | ±2n | Yes for average; not at rest. Period formula structural, general rate/recurrence proved. |
| 2,3 / four rules | Flipping scatterers | T below; R=T/2 | 43/2 | ±T/2 in finite census | Yes for average at all n (`recurrent_half_two/three`, `rate_robustness`). No at-rest cycle in tested sizes. |
| 4 / both | Two-site bounce; marker flips | 4; 4 | 43 | 0 | Yes at all n; exceeds the old strict count ceiling (physical identification open). |

| Odd n | Kind 2/3 primitive periods T (both directions) | R=T/2 |
| --- | --- | --- |
| 3 | 24 | 12 |
| 5 | 80 | 40 |
| 7 | 56,168 | 28,84 |
| 9 | 288 | 144 |
| 11 | 88,440 | 44,220 |
| 13 | 208,624 | 104,312 |
| 43 | Finite recurrence and average 43/2 proved; primitive periods/winding not classified. | T/2 |

Support has two counts: visited sites and the union of all nonvacuum sites over the
cycle, including spectator markers. The static gap visits d+1 sites; the single mirror
and circulating families visit n; the saturated bounce visits 2. A finite ring alone
is not a localization theorem on an infinite substrate. No support cutoff is imposed.
If the 43-state clock phase is retained too, use lcm(T,43) and scale R accordingly;
the average is unchanged. Lifted displacement counts signed steps, not position modulo n.

| Lean result | What it certifies |
| --- | --- |
| `closed_half_rate_two/three` | Marker-population balance forces 2R=T on every closed cycle, all n. |
| `packet_periodic`, `recurrent_passive/half_two/half_three/saturated` | Every finite one-packet state recurs with its stated rate. This is not attraction/self-correction. |
| `saturated_four_return`, `saturated_four_displacement`, `saturated_resting` | Four-tick return, zero lifted displacement, average 43; all n. |
| `AutonomousCensus43`: `mirror43_minimal`, `mirror43_resting`, `mirror43_not_robust` | Native minimal period 86, R=2, average 1, at rest; removing the marker gives average 0. |
| `native_average_bound` | Every single-packet native average is ≤43, independent of cycle length. |
| `and_or_marker_embeddings`, `static_receiver_collision` | AND/OR port dynamics both compress to kind 0 with the scalar guard retained. Full two-request states lie outside the eight-state alphabet. |

In the fixed OR chart `(m,false)`, AND always bypasses and is outside the admissible
space (`and_in_or_chart`, `fixed_or_chart_and_excluded`). The AND embedding `(m,true)`
is a different chart, not an invertible reconstruction of the two original requests.

The lightest static at-rest count is 43/n (1 at n=43), but it is not marker-robust
and visits the whole ring. The robust at-rest kind 4 count is 43, but it saturates
43 updates. Thus no robust, unsaturated electron is selected in the tested sizes.
At n=43 this statement is proved for the exhibited static witness and kind 4;
kind 2/3 winding and general static minimality still need formal classification.
`nonstatic_no_unit_average` excludes mean one for kinds 1–4 at ALL n, regardless
of the unresolved winding.

## Component contracts

| Part | What to read | Module notes |
| --- | --- | --- |
| Six pillars and port limits | Check the inputs and outputs for each part. | [Components](Components.lean), components, pillars, interactions and classification |
| Joint update and headroom | The packet-bank action is supplied. The lift projects to the core. The margin uses the same units as the load. | [Components](Components.lean) and [Values](Values.lean) |
| Receiver outputs | A visit can deliver a live value, a record or a comparison flag. The consumer must name its input. | [RingReceiver](RingReceiver.lean) and [Interface](Interface.lean) |
| Flags, exports and costs | Compare traces only after the booked events and their units are fixed. | [BoundaryErasure](BoundaryErasure.lean) and [LocalController](LocalController.lean) |

## Admission

| Question | Where to read |
| --- | --- |
| Which start and supply are given? | [OddReferenceSource](OddReferenceSource.lean) and [OpenHandoff](OpenHandoff.lean) |
| What can the clocked trials reach? | [ClockedRootTrials](ClockedRootTrials.lean). The four histories keep both request bits. |
| Which guards are reversible? | [LocalController](LocalController.lean). Compare the tagged trace with the mixed input. |
| What reaches the reader? | [Interface](Interface.lean) and [RingReceiver](RingReceiver.lean). The receiver rule can change a port or a flag. |
| What can the boundary erase? | [BoundaryErasure](BoundaryErasure.lean). The account counts only a supplied export. |

The parked [joint-successor work](TODO.md#reachable-occupied-background) concerns the closed
resource-exchanging execution for decay. It does not define held-event mass. The clean backward reference stream is a supplied
input. Its renewal by the occupied vacuum and its return within one period
are not certified. EP's `ExcitationPersistence` records the exact missing
joint execution and resource account. Zero retained-ring erasures and a
reversible packet lift do not fill this contract.

## Constraints on occupied joint successors

`JointSuccessorConstraints` audits the admissibility contract before a joint
successor is selected. The generic `Components` core has not been identified
with a packet-free physical background. Its one-way projection does imply
packet-independent core trajectories. It does not imply zero gross use of
resources that can be replenished during the same period.

| Question | Checked result or missing definition | Lean entry point |
| --- | --- | --- |
| One-way projection | Equal initial backgrounds have equal background endpoints for all packet banks and horizons. | `packet_independent_background` |
| Resource debit | An identified net loss in a background-only reserve is packet-independent. A zero-bank baseline with zero net loss forces zero net loss for all banks. This is conditional on that account and baseline. | `net_debit_independent`, `zero_baseline_forces_zero_net_debit` |
| Gross consumption | Positive matched consumption and intake can maintain a constant reserve. Capacity alone does not force zero gross consumption. | `positive_matched_flows`, `PMSubstrate.Pillars.capacity_sustains` |
| Conservation and activity | A one-way FIFO preserves packet population, changes an occupied slot and returns the bank in 43 ticks with a fixed background. This algebraic example is not an admitted physical successor. | `one_way_reversible`, `fifo_population_conserved`, `fifo43_nontrivial`, `one_way43_return` |
| Reversibility clause | `Equiv.Perm` supplies the required notion. | `Components.joint_bijective_iff` |
| First missing clause of A | No locality/primitive-root-event predicate classifies arbitrary background × packet-bank permutations. The existing ticks certify their own operations and stencils. | `RecordTransport.tick_local`, `RingReceiver.tick`, `ClockedRootTrials.quiet_trial_tick` |
| Joint charges and labels | Component readouts exist. The total readout on the proposed physical joint state is not identified. | `Components` component contracts |
| Closure clause | Weight invariance is the SCOPE premise. Successor equivariance also needs a joint group action and its justification. G₊ fixes `cu` but need not fix the 43-state reading. | `ClockSymmetry.Gplus`, `swap_changes_clockReading` |
| Empty and clamped cases | An algebraic zero bank exists. A physical no-packet embedding, stationary-family joint encoding and clamping operation remain unspecified. | `Components.PacketBank`, `OddReferenceSource.rest_stationary` |
| Finite reduction | Finite cell/channel indices still give an infinite complex-valued packet state. No faithful finite admissible-successor implementation family is specified. | `packetBank_infinite` |

The requested zero-gross-consumption no-go is not derived. Back-reaction can
be required by a packet-dependent background-resource account, once that
account and its no-packet baseline are identified. It does not follow from
reversibility and period balance alone. The set A is not filled with placeholder
predicates. It is not classified as empty, unique or a family. No selected
successor, loaded-seed derivation or coset-0 contact count follows yet.
The [joint-successor TODO](TODO.md#reachable-occupied-background) names the missing inputs.

## KAutomaton closeout

The conditional joint update, port contract and least-cost rule are in
[Interface](Interface.lean), [Components](Components.lean) and [RingReceiver](RingReceiver.lean).
Admission, clock placement, tariffs and supply stay as named inputs.

<a id="bare-line-stabilizer"></a>

The [bare-line stabilizer](Components.lean) gives the checked E7 generators,
their sector action and the reference for the group orders.

## Native machine

The [machine module](Machine.lean) lists the implementation and its certificates.
The machine builds with PMAction. The packet interface imports it from above.

| Area | Entry modules |
| --- | --- |
| Carriers, parity and vacuum | `CarrierEvents`, `CarrierParity`, `CarrierVacuumSector`, `VectorEvenFrame` |
| Registers, controls and readout | `IndependentRegisters`, `RegisterControl`, `ScheduledReadout`, `InterferenceReadout` |
| Root transfers and reference | `RootTransfer`, `RootTransferPhase`, `RootReferencePreparation`, `NativeReferenceBackground` |
| Records and supply | `RecordTransport`, `RecordSupply`, `OpenReferenceFlow`, `PrimitiveRecordBoundary` |
| Clock and microscopic hop | `ClockRing`, `ClockControlledRoot`, `ClockDynamics`, `AxisHop`, `SliceHop` |
| Native links and locality | `NativePacketUpdate`, `NativePacketRouting`, `NativeCoherentLinks`, `EdgeLocality` |
| Refresh and repair | `RootMaintenance`, `FactorRepair` |
| Finite paths and limits | `FiniteRootWordControls`, `FiniteConfigurationControls`, `NativeConsistency`, `CompactLimits`, `MatterContinuum` |

<a id="node-handoff-and-admittance"></a>
<a id="two-site-handoff-and-the-six-pillars"></a>

## Handoff

| Check | What it gives | Lean names |
| --- | --- | --- |
| Tagged and mixed starts | Tagged starts give the same trace. A mixed start can change a destination and its flag rate. | `LocalController.tagged_trace_observable_eq`, `mixed_open_receiver_destinations`, `RingReceiver.mixed_ring_registration_rate` |
| Local guards | Classify the reversible rows. Two distinct tables give the same tagged open trace. | `LocalController.radius_one`, `receiver_realisation`, `reversible_iff_rows`, `enumerated_rule_count`, `two_open_compatible_rules` |
| Carrier and port routing | Read the native update on the supplied ports. Each site has two live modes and two record modes. | `NativeCarrierProtocol`, `NativePacketRouting`, `NativePacketUpdate`, `TwoSiteHandoff.port_count` |
| Exchange and bypass | Trace the live and record destinations. A supplied root half-pulse realizes exchange. | `TwoSiteHandoff.step_trace`, `export_trace`, `receiver_half_pulse`, `OpenReferenceFlow.exchange_reflects`, `bypass_transmits` |
| Closed pair | Four exchanges return the full state. Four restorations need the reference in all four slots. | `TwoSiteHandoff.first_reference_iff`, `second_reference_iff`, `exchange_four_returns`, `four_restorations_iff` |
| Through weight | The current law gives the through weight. Product weights need independent steps with equal weights. | `HandoffAdmittance.node_current`, `through_eq_conductance`, `direct_crossing_prob`, `Interface.Handoff.through_weight_eq_alpha` |
| Pulse calibration | Read the principal exchange area on a through pulse. The clock duration and wall-rate conversion remain inputs. | `Interface.Handoff.principal_through_area_eq`, `HandoffAdmittance.two_pass_alternative`, `reflected_event_ne_alpha`, `pulse_calibration_transfers` |

<a id="open-route-and-reference-supply"></a>
<a id="odd-rest-modes-as-occupied-reference-candidates"></a>

## Record

| Check | What it gives | Lean names |
| --- | --- | --- |
| Coherent recording | Unequal outputs with overlap need orthogonal records. A supplied reversible reset stores the displaced state. | `CoherentGate.unequal_needs_orthogonal`, `CoherentRecordRestoration.prepared_repair`, `unitary_reset_factorization`, `twice_undoes` |
| Open line | Trace arrivals and exports for each supplied visit. A three-site start fixes only the first visit. | `OpenHandoff.address_step`, `receiver_trace`, `export_trace`, `any_incoming_trace`, `neighbours_do_not_determine_second_visit` |
| Readiness | Check the supplied population and accepted error. Distinguish an open orbit from a finite ring return. | `OpenHandoff.acceptance_iff_supply`, `population_required`, `basis_loading_iff`, `RecordSupply.open_orbit_forever`, `ring_returns` |
| Odd reference | The sharp seed fails the odd-sector test. A supplied occupied rest mode can load the ready port. | `OddReferenceSource.basis_label_not_odd`, `root_phase_word_no_basis`, `rest_stationary`, `rest_population`, `first_wall_ports`, `odd_seed_train_restores` |

## Cost

| Check | What it gives | Lean names |
| --- | --- | --- |
| Request complement | One visit has a complement identity. A clocked trace need not have this symmetry. | `LocalController.complemented_output`, `receiver_dual_not_conjugate`, `receiver_dual_flag_counterexample` |
| Erasure | A booked binary reset counts one bit. The retained ring exports zero bits. | `BoundaryErasure.erasing_pays_one`, `erasedBitsPerTick`, `ring_cycle_erasure`, `tagged_rule_exports` |
| Closed-ring selection | Enumerate the finite orbits. Both rules attain the least registration rate on the certified family. | `RingReceiver.orbit_enumeration_covers`, `orbitRegistrationRate`, `minimum_orbit_registration_rate`, `both_rules_attain_best_survival` |
| Weighted visits | Sum the flags with the supplied visit weights. Uniform ports give zero exchange flag cost. | `LocalController.traceExchangeFlagCost`, `uniform_trace_exchange_flag_cost`, `uniform_remaining_cost_iff` |
| Booked events | Group registrations by owner. Add the bits erased at the boundary. | `NetCost.expected_count_linear`, `Components.booked_registration_and_erasure_sum` |
| Root attempts | Multiply the Bernoulli attempt law by the uniform carrier law. The expected cost includes the active carrier fraction. | `RootTransferAccounting.rootAttemptPMF`, `root_attempt_pmf_normalized`, `expected_root_cost` |
| Selection and refresh | Compare the supplied families and prices. A least-cost refresh uses the required job ledger. | `PersistenceSelection.within_family_iff_cheapest`, `RefreshSchedule.minimal_is_ledger`, `CoherentRefresh.minimum_once` |
| Reference comparisons | Read the conditional output and balanced-reset thresholds. | `Values.outputFlagThreshold_eq`, `balancedResetThreshold_eq`, `WireReferenceCost.balanced_reset_gap_eq_values` |

<a id="calibrating-the-root-clock"></a>

## Clock

The period is `PMSubstrate.E8Values.Delta`. The [machine clock geometry](Machine/ClockRing.lean)
uses the substrate lattice pairing. The [clock values](Values.lean) keep the word lengths and
rate ratios. The [interface notes](Interface.lean) give the supplied clock placements.

| Check | What it gives | Lean names |
| --- | --- | --- |
| Period | One full clock has 43 phases. A closed mask excursion can fire in two phases. | `E8Values.Delta_eq`, `ClockControlledRoot.cycle_closes`, `CarrierReferenceCycle.excursion_boundaries` |
| Serial words | The root half-pulse takes two quarter-times. Word bounds use the stated serial schedule. | `RootTransferPhase.half_pulse_word`, `Values.shortSerialTicks`, `longSerialTicks` |
| Alias and calibration | Integer samples can identify several gaps. A trial statistic or a principal-range witness fixes the calibrated gap. | `RootClockCalibration.phase_alias_iff`, `trial_weight_inj`, `gap_from_trials`, `principal_flag_inj` |
| Two retained trials | The request pair fixes the endpoint. The four histories do not supply their own physical prior. | `ClockedRootTrials.pair_endpoint`, `historyCount`, `all_pairs_history_count`, `shared_request_history_count`, `history_pmf_factorizes` |
| Common clock | A supplied relation between a statistical pair and two ticks sets the generator per tick. A common tick cancels from the rate ratio. | `ClockedRootTrials.phase_in_ticks`, `CertainTransferRate.common_tick_rate_ratio`, `Values.equal_normalization_rate` |
| Clock-plane projection | Read each coset's drift per lap. The vector class has transverse-silent closure. | `ClockPlaneProjection.cospinor_lap`, `spinor_lap`, `vector_self_closing`, `self_closing_iff` |

<a id="heavy-label-application"></a>

## Full clock-root symmetries

The clock root is `ClockPlane.cu`. The full 43-state reading also uses `cv`.
Do not apply a root-stabilizer invariance statement to that reading without
checking the second clock vector.

| Object | Definition or result | Lean entry point |
| --- | --- | --- |
| Ambient group | All products of E8 root reflections act as integral lattice isometries. | `ClockSymmetry.Weyl`, `rootReflection`, `weyl_norm` |
| Full G₊ | Keep both aligned D4 factors and fix `cu`. Sector preservation is commutation with twice the orthogonal projector. | `Gplus`, `projector_sectors`, `maps_spacetime`, `maps_internal` |
| Full G± | Keep both factors and fix `cu` up to sign. | `Gpm` |
| Quotient | D4 plus D4 has index four. Both factor discriminants receive the same permutation. | `sector_annihilator`, `keyAction_descent`, `diagonal_glue` |
| Glue image | Both full groups induce exactly identity and the spinor-key swap. The clock key (0,1) is fixed. | `full_generation_image` |
| Generators | Six D3 reflections and a two-root glued word generate G₊. An eight-root negation word extends it to G±. | `ClockSymmetryGenerators`, `positive_generators_exhaustive`, `line_generators_exhaustive` |
| Normal form | Each factor permutes and signs its three transverse axes. The two outer signs agree. | `ClockSymmetryNormalForm`, `ClockSymmetryFrames`; `spatial_frames`, `integral_sign_parity` |
| Orientation | The same nontrivial glue swap has spatial determinants -1 and +1. | `swap_orientations` |
| Clock limit | The displayed swap does not preserve the reading that uses `cv`. | `swap_changes_clockReading` |

The [EP generation table](../PMElementaryParticles/OVERVIEW.md#generation-orbits)
adds the existing generation-specific channel placement. This is a separate
restriction from the bare clock root and the two factors.

## Route

| Check | What it gives | Lean names |
| --- | --- | --- |
| Wall pairs | The omitted class labels the packet. A crossing word acts on the two walls. | `GenerationWalls.one_class_per_wall`, `GenerationEncoding.carriers_per_packet_card`, `GluedRegister.crossing_word_glued` |
| Stationary reference | The stated node model gives the direct and two-leg routes. A stationary reference and the route admission remain inputs. | `ReferenceClassHop.stationary_iff`, `ReferenceNode.restoring_two_classes`, `direct_three_classes`, `restoring_series` |
| Heavy label | A supplied companion seed permits a guarded crossing. The setup has conditional flag sums on the active and static sides. | `ElectricCompanionBank.guarded_companion_transport`, `ElectricCompanionSetupFlagCosts.primitive_setup_sum` |

### Implementation imports

| Reader | Implementation it uses |
| --- | --- |
| `ControlledGluedRegister`, `DoubletSign` | `GluedRegister` and `CarrierWeyl` |
| `RefreshMap`, `HeavyFlipNativeBoundary` | `ClockControlledRoot` and `InBandRootReadout` |
| `ElectricCompanionBank`, `ElectricChiralKick`, `ElectricHeavyRecord` | `CarrierTriality`, `RegisterInteraction` and `RootBranchEncoding` |
| `ReferenceSafeRestoration` | `RootOrderComparison` |

## Reversibility boundary

Keep the records in the reversible state until their last use.
The comparison flag is an observation. A booking determines whether it is paid.
A separate export can be kept, returned or erased. The retained update and the
boundary operation have different hypotheses. See [BoundaryErasure](BoundaryErasure.lean).

The packet interface follows PMConstants. The machine modules build with PMAction.
The [dependency audit](../AuditDependencies.lean) checks these boundaries.
