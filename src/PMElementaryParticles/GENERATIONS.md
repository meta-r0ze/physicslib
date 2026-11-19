# Generations on the E8 wire

| Reading | What fixes it | Count, order and heavy state | Protocol dependence |
| --- | --- | --- | --- |
| Glue address | `GenerationWalls.one_class_per_wall`, `GenerationOrientation.type_label`, `ControlledGluedRegister.wallClass` | The three nontrivial D₄ glue classes label three pairs. Each pair omits its own class. The glue structure gives a cyclic action and leaves mass ordering open. | Each address carries the same 16-channel inventory. |
| Wire route | `ReferenceClassHop.stationary_iff` and `touches_reference_class`, `HeavyFlipControl.direct_iff`, `ReferenceNode.restoring_series` | One address has a direct insertion and two need the reference node. The direct address is `g = 0`, which supplies the unsuppressed row in the normalized bare mass matrix. The two restoring addresses have equal link weight. The middle and lightest masses are modes of the coupled matrix. | The route test uses the wall classes for every label. The bare mass matrix is shared. |
| Tier ledger | `TierLedger.tiersFor` and the four length lemmas, `QuarkMasses`, `LeptonMasses` | Each protocol lists three tiers in ascending order. The highest occupied tier is 3 for up and 2 for down, electron and neutrino. Neutrino masses remain open. | Up uses `{0, 2, 3}`. Down, electron and neutrino use `{0, 1, 2}`. The assignments are model inputs. Their formulas use the substrate's `Δ = 43`. |

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

### Comparison only — declared ledger ratios

With the substrate value of `α`, the bare wire gives `m₂/m₃ ≈ 0.192/Δ`.
The declared formulas give about `0.316/Δ` for up, `0.962/Δ` for down,
and `2.557/Δ` for electron. For `m₁/m₂` they give exactly `3/Δ²` for up,
about `2.126/Δ` for down, and about `0.208/Δ = 8.94/Δ²` for electron
at the stated period. See [tier arithmetic](../../tools/tier_route_check.py).
