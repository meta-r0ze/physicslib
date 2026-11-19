# Generations on the E8 wire

| Reading | What fixes it | Count, order and heavy state | Protocol dependence |
| --- | --- | --- | --- |
| Glue address | `GenerationWalls.one_class_per_wall`, `GenerationOrientation.type_label`, `ControlledGluedRegister.wallClass` | The three nontrivial D₄ glue classes label three pairs. Each pair omits its own class. The glue structure gives a cyclic action and leaves mass ordering open. | Each address carries the same 16-channel inventory. |
| Wire route | `ReferenceClassHop.stationary_iff` and `touches_reference_class`, `HeavyFlipControl.direct_iff`, `ReferenceNode.restoring_series` | One address has a direct insertion and two need the reference node. The direct address is `g = 0`, which supplies the unsuppressed row in the normalized bare mass matrix. The two restoring addresses have equal link weight. The middle and lightest masses are modes of the coupled matrix. | The route test uses the wall classes for every label. The bare mass matrix is shared. |
| Tier ledger | `TierLedger.tiersFor` and the four length lemmas, `QuarkMasses`, `LeptonMasses` | Each protocol lists three tiers in ascending order. The highest occupied tier is 3 for up and 2 for down, electron and neutrino. Neutrino masses remain open. | Up uses `{0, 2, 3}`. Down, electron and neutrino use `{0, 1, 2}`. The assignments are model inputs. Their formulas use the substrate's `Δ = 43`. |

The physical route, heavy writer and lightest-offset branch depend on
Transport's [Admission](../PMTransport/PREMISES.md#admission).
[Absolute timing](../PMTransport/PREMISES.md#absolute-timing) and the
[Registration tariff](../PMTransport/PREMISES.md#registration-tariff)
supply the elapsed and paid costs of that trace.

## From glue address to route

In the glued register T is static and F is active. In
`ControlledGluedRegister.wallClass`, the Boolean is the activity flag, so
T uses `false` and F uses `true`. The class indices are vector `0`, spinor
`1` and conjugate spinor `2`.

| Glue address | Static T, `g + 1` | Active F, `g − 1` | Reference-wall insertion |
| --- | --- | --- | --- |
| 0 | 1 | 2 | Direct |
| 1 | 2 | 0 | Through the node |
| 2 | 0 | 1 | Through the node |

The direct condition is that neither endpoint class is the reference class
`0`. This is the predicate in `HeavyFlipControl.direct`.
`ReferenceClassHop.touches_reference_class` proves that the pair contains
`0` exactly when `g ≠ 0`. The glue-pair-to-route link already follows.
The reference breaks triality by occupying a chosen class. In the conserving,
Hermitian exchange model its stationarity excludes the direct exchange on
the light chirality when that exchange touches its class.

In the conserving node model, each restoring move uses two equal legs with
admittance `α`. One node passage gives `k/K = α/2` by
`ReferenceNode.restoring_series` and `NodeAmplitude.node_series`. Free
spectator ports preserve this value. The direct route has zero node passages
and is normalized to `K = 1`. Reading admittance as a Hamiltonian rate needs
the event law described in `NodeAmplitude`.

A wall step preserves glue class (`GluedRegister.wallStep_class`). The
same-generation endpoint exchange changes glue class and has a certified
six-reflection word on the glued register (`crossing_word_glued`,
`ControlledGluedRegister.runCrossing_encode`). The equal-class **gapped**
crossing instead shifts the address by `+2` from T to F and preserves the
signed label. Its certified word uses four swap reflections and two parity
reflections (`GappedGluedCrossing.equalClass_iff`, `runGappedCrossing_encode`
and `forward_entry`). The three- and one-reflection counts in
`tools/event_clock_check.py` concern specific single-carrier endpoints.
They give neither the word lengths nor lower bounds for the glued-register
operations. These crossings and the on-wall node insertion count different
operations.

## Where the readings agree

The glue and wire readings share the three addresses. They give two route
classes, with one direct address and two restoring addresses. The ledger
also has three entries per protocol. Its sorted entries can be compared with
the sorted wire masses, with no derived individual assignment of the two
restoring addresses to the two light mass ranks.

For the normalized bare Schur mass, take the other-wall cycle to have unit
weights and use the resonance `δ = −1`. In coordinates with the direct
row first, write `M = D(−I + P)`, where `D = diag(1, k, k)` and `P` is the
three-cycle. Then `MM† = D(3I − J)D`, where `J` has all entries one.
The Gram matrix has a zero eigenvalue, the vector `(0, 1, −1)` has
eigenvalue `3k²`, and the trace gives the remaining eigenvalue `2 + k²`.
For `0 < k < 1`, the sorted singular values are therefore
`0, √3 k, √(2 + k²)`. The leading heavy-to-middle factor is
`√(3/2) k`. Its exact ratio is `√3 k / √(2 + k²)`.

In the substrate impedance model, `Z = πΔ + O(1)` when counting powers of
the period with the other parameters fixed
(`PMSubstrate.Impedance`'s `capacityTerm` and `impedance`).
Consequently one node passage gives one leading inverse power of `Δ`.
The ledger's highest two tiers are also one power apart for each protocol.
This agreement is about the leading power.

The bare wire has an exact lightest zero at resonance. The ledger assigns
a nonzero lightest charged mass and places the lowest two tiers two powers
apart for up and one apart for down and electron. The charged formulas
combine powers with coefficients and corrections. One value at `Δ = 43`
cannot distinguish a first-order law with a small coefficient from a
second-order law with a larger one.

## The charged lift

The existing candidate acts on the static wall. `vector_static_leg`
places it at `g = 2`, where T carries the vector class. This is an
insertion address. The zero mode belongs to the whole wire.
`ChargedInsertion.select_static` uses two phase-matched comparisons for
each charged protocol. The target is `i` for electron, `−1` for up and
`−i` for down. Every matching channel is retained with amplitude one,
including every colour of the matching quark protocol.
`joint_selector` restricts this readout to the static vector leg.

| Charged protocol | Static address | Comparisons in the selector | Additional node passages and wall crossings in the on-site model |
| --- | --- | --- | --- |
| Electron | 2 | 2 | 0 and 0 |
| Up | 2 | 2 | 0 and 0 |
| Down | 2 | 2 | 0 and 0 |

The last column counts only the support of the added diagonal term. Its
two endpoints are on T at the same address. The reference node belongs to
the F insertion, so this local term adds no node passage and no crossing
reflections. The Schur response still uses the existing gapped crossing
link and reference-side factor. A term in the Schur product uses one
inverse gapped link. That link has the reverse support of the certified
six-reflection crossing, for every signed label. The reference factor
contains the same zero- and one-passage routes for all three protocols.
These are counts in the given circuit and factorization. Primitive
comparisons, pulse admission and timing would need a native schedule
before one could claim a shortest native route or count its reflections.

At fixed nonzero bare resonance,
`ChargedInsertion.det_flip_at_resonance` gives exactly `δ² ε` on every
selected static channel. `ResonanceLift.shifted_full_zero_iff` and
`ChargedInsertion.full_zero_iff_unselected` give an exact lift for any
nonzero supplied offset when the crossing and reference flip are
invertible. With a positive cycle product, `calibrated_detuning` pins a
shared real detuning if an unmodified calibration channel stays
stationary. If the detuning can vary independently, the wall can retune
to a zero (`ResonanceLift.negative_retuning_exists`).
`det_shifted_eq_uniform_iff` matches a uniform shift by
`ε = 3t + 3t²/δ + t³/δ²`. Its first-order coefficient is the same for
every address and protocol. The matching concerns the determinant. The
spectra can differ (`det_matched_trace_gap`).

In the normalized bare Schur model above, the lifted determinant has
magnitude `k² |ε|`. Since the other two singular values tend to
`√3 k` and `√(2 + k²)` at fixed positive `k`, their product with the
lightest singular value gives
`m₁/m₂ = |ε| / (3 √(2 + k²)) + o(|ε|)`.
Thus all three charged sectors respond at first order in their offset.
The two factors of `k` in the determinant come from separate rows of the
common reference factor and cancel from the leading light-to-middle
ratio. If an insertion law supplies one or two inverse powers of `Δ` in
`ε`, the ratio inherits that order at leading order in the offset.
The selector and route supply no such power for the offset.

This excludes the bare route counts as the source of the ledger's
protocol-dependent lightest step. In this candidate any such difference
must enter through the label-sensitive pulse or other protocol-dependent
dynamics, such as a difference in the maintained detuning. A native
selection and firing law, the offset's scaling, and the existence of
shared calibration remain open. Three addresses, two route classes and
three ledger entries therefore describe different features of the model.
The current results give no identification of a generation with a
protocol's number of `Δ` steps.

### Phase, handoff and Toll

At `t = 3π/4`, the static hypercharge tags give angles `0, −3π/2, π,
−π/2` for vacancy, electron, up and down. Their eigenphases are
`1, i, −1, −i`. The shortest angular distances from phase one are
`0, 1, 2, 1` quarter-turns. For the electron, this distance already
discards a full turn of the signed difference between `−3π/2` and
`π/2`.

The transport at this parameter is diagonal
(`VacancyProjection.hypercharge_eq_diagonal`). It multiplies each label
by its phase in one application of the packet operator and keeps the
label's position. The relative
phase labels a channel and specifies the correction applied to the
transported branch of the comparison. The packet has no handoff edge
for each quarter-turn. In the existing pulse implementation the same
branch rotations appear for any controlled transport
(`BranchPulseContract.program_correct`). Continuous branch rotation,
the controlled transport and the conditioned flip still require native
admission and pricing.

There are two different comparisons at the same transport parameter.

| Static label | Shortest angular distance in quarter-turns | Vacancy-relative flag probability at `t` | At `2t` | Flags when this label is the matched target |
| --- | --- | --- | --- | --- |
| Vacancy | 0 | 0 | 0 | 0, 0 |
| Electron | 1 | ½ | 1 | 0, 0 |
| Up | 2 | 1 | 0 | 0, 0 |
| Down | 1 | ½ | 1 | 0, 0 |

The vacancy-relative columns follow from
`ProtocolToll.selector_step_flags`, `flags_three_quarter` and the
vacancy flag lemma. The first column of flags happens to be half the
angular distance. These are expectations from one test. They provide
no count of successful handoffs. An equal-price schedule that charges
both uncorrected flags separately would give scores `3/2, 1, 3/2` for
electron, up and down. The actual selector uses the two *matched*
comparisons. `ChargedInsertion.matched_flags_zero` proves their
selected flags vanish, and `select_static` gives unit retained
amplitude. This leaves the cost of carrying out the comparison and
maintaining its controller open.

In the spatial handoff model, `HandoffAdmittance.handoff_from_conductance`
identifies `α` as the through probability. The unique all-pass history
of `q` timed layers has probability `α^q` under independent through
weights (`direct_crossing`, `direct_crossing_prob`). Its coherent
amplitude magnitude, if that history carries the insertion, is
`α^(q/2)`. Even taking the angular count as a layer count would then
give orders `Δ⁻¹` for up and `Δ⁻¹ᐟ²` for electron and down. The
`α/2` of a two-leg conserving node is a different calculation. It is
an effective series admittance (`NodeAmplitude.node_series`).

For a scheduled unflagged wire, the survival model gives amplitude
`exp(−T/2)` for a Toll `T` measured in expected registrations
(`TollAmplitude.wireAmplitude`). Suppose a schedule charges the single
uncorrected comparison with weight `w` and has a common baseline. Its
relative amplitudes are then `exp(−w/4)` for electron and down and
`exp(−w/2)` for up. This gives a square relation. A fixed weight gives
constant relative factors as `Δ` varies. An `α, α²` pair would require
`w = 4 log(1/α)` for exact equality, by
`ProtocolToll.selector_half_flag_weight_iff`. For leading powers the
weight would need that logarithmic growth up to a bounded term, and
the common insertion scale would also have to be accounted for. The
flag calculation supplies neither the schedule nor its weight.

Amplitudes multiply along a specified coherent history. A probability
product and a survival amplitude can describe the same attenuation
if the effective negative log of that probability is used. Identifying
that log with the expected-registration Toll needs a physical derivation.
The insertion channel and its offset's inverse-period order remain open.

A common source for the heavy weight and the light lift would need a
native record-and-fire schedule with both placements. The conditional
two-bit heavy record has flag budgets `2, 0, 1` for electron, up and down
(`HeavyFlipRecords.orbit_record_tolls`). With a positive price per flag
it makes up the least attenuated, whereas the single vacancy-relative
flag makes up the most attenuated. The shared auxiliary hypercharge
readout on the two walls cannot write the heavy record's quark bit
exactly (`HeavyFlipRecords.no_exact_quark_record`).

### Comparison only — declared ledger ratios

With the substrate value of `α`, the bare wire gives `m₂/m₃ ≈ 0.192/Δ`.
The declared formulas give about `0.316/Δ` for up, `0.962/Δ` for down,
and `2.557/Δ` for electron. For `m₁/m₂` they give exactly `3/Δ²` for up,
about `2.126/Δ` for down, and about `0.208/Δ = 8.94/Δ²` for electron
at the stated period. See [tier arithmetic](../../tools/tier_route_check.py).
