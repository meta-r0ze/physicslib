# PMElementaryParticles — overview of checked results

Why continuum phase space is correct on a lattice substrate, and when it is not: [`CONTINUOUS.md`](CONTINUOUS.md).

The single map of what Paper V proves and what later work can reuse. Open work is
in [`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md); build instructions are in
[`README.md`](README.md). Sources are under `PMElementaryParticles/`, imported by `PMElementaryParticles.lean`.
Theorem names are entry points, not exhaustive lists; the Lean source is ground
truth. Library order: PMSubstrate → PMAction → PMConstants → PMElementaryParticles → PMFlavor → PMHadrons → PMAtoms → PMCosmology (`AuditDependencies`). This folder imports nothing from PMFlavor.

## Scope

Paper V models **elementary-particle protocols and their decay** on the E8
substrate. It supplies: the V−A contact amplitude and its `W`-exchange origin, the
muon and massive-daughter decay widths with phase space derived from the Lebesgue
measure on `ℝ³` (`PolarMeasure`, `PairSphere`, `ElectronMeasure`), the decay-law
relation to Paper I survival, and the particle/mass/charge protocol checks against
data (recorded as tensions, not fits). It does **not** select the physical
interaction, the flux `1/(2m)`, the radiative factor, or the particle ledger; those
remain model inputs.

Hadron-level modules (composite masses, composite states and transitions, pion/kaon/neutron
widths, the particle channel inventory) live in [`PMHadrons`](../PMHadrons/OVERVIEW.md).
Downstream libraries import `PMElementaryParticles.Values` (like `PMSubstrate.E8Values`,
`PMConstants.Values`, `PMFlavor.Values`): `me`, `hbarc`, `electronTime` (+ `electronTime_tight`),
`αe`, `αinv`, `fermiME` (+ `fermiME_tight`), `muon`, `tau`, the six quark masses and the muon/tau
lifetimes in seconds, with their bounds. Prove a bound there once rather than inline.

Shared units and couplings used by every level are in `SharedUnits` (`me`, `ħc`, `α`, `α⁻¹`,
their bounds, and `G_F` in `m_e⁻²`).

## Protocols are not wire modes

The odd carrier modes of a class are the wire's Dirac components, four axes × two walls (`PMAction.CarrierVacuumSector`), and colour cannot act on them while commuting with `β` and the `αⱼ` (`PMAction.ColourRegister`). So protocol identity (lepton or quark, colour, weak partner) is a separate register; the 16-carrier packet is its count and gauge actions. Earlier readings that put the lepton pair on axis `0` and the up/down pair of colour `i` on axis `i` of the wire are withdrawn: `BetaReference` and `UpDownWire` (modules removed), `DoubletSign`'s wire-mode count, `ProtocolReadout`'s carrier-state reading, `CycleReadout`'s weak-pair reading, and the reference-hold test (module removed). Their theorems remain as carrier and matrix facts; the partner difference has to come from the protocol register.

## Glued protocol register

The diagonal glue in `E₈ = D₄ ⊕ D₄` supplies two carriers of the same class per
glued root. Following `GenerationWalls`, wall T of generation `g` uses class
`g + 1` and carries the amplitude in the first factor. Wall F uses class
`g − 1` and exchanges the roles of the factors. `GluedRegister` verifies that
triality followed by factor swap takes T to F, and certifies the six-reflection
word on all 240 roots (`crossing_word_glued`, `crossing_word_pure`).

`ControlledGluedRegister` checks this placement against the EP inventory. Fix a
generation and use F as the active wall, consistent with the second-wall
convention of `WallChiralCurrent.kernel_projector`. Activity and the
signed-axis index identify all 16 channels bijectively. The positive lepton
label means neutrino on F and vacancy on T. Each channel and amplitude index
encodes into a distinct glued root. The weak relabeling applies the antipode
only on F, and colour permutations use the vector-frame action transported
by triality. A glue-class-controlled pure root reflection moves the amplitude
while preserving the channel and fixing the other wall in that generation. In particular,
`weak_active` shows that the weak toggle preserves the active bank.

The swap-plus-triality word preserves the signed axis, colour permutations and
electric charge. It changes the glue class to stay in the same generation.
`eq_opposite_iff` identifies the unique opposite-bank partner from the
signed label. `runCrossing_neutral` sends the static neutral slot to the
active neutrino with the same amplitude index, giving the `ν_R → ν_L`
channel pairing. The inventory still calls the static slot a vacancy for
the light-state projection. For every forward pair the static-minus-active
hypercharge is `+1` on even signed indices and `−1` on odd indices
(`opposite_hypercharge_step`, in the packet's integer `3Y` tags).
The magnitude and sign agree with the existing scalar link and its
conjugate from `PMConstants.SectorLinks` (`opposite_scalar_link`).
For the neutral Dirac bilinear the conjugate insertion balances the
static-minus-active difference of `+1`. This fixes the charge budget for
using the reference link on the glued pair.
`no_protocol_preserving_wall_exchange` concerns the separate inventory
names. `no_root_only_wall_readout` shows that a root can occur on opposite
walls in different generations, so the class control uses the generation.

At fixed generation, reversing the ordered live and companion classes
exchanges the banks. The weak refresh instead changes the signed label on
the active bank. Flavor proves the distinction for its tagged in-cycle word
in `OrientationDoublet.selected_inCycle_preserves_orientation`.
[Flavor overview](../PMFlavor/OVERVIEW.md#wall-orientation-and-weak-refresh)

### Equal-class gapped crossing

`GappedGluedCrossing` identifies the word with the support of the existing
gapped hop. The forward leg keeps the glue class, takes T at generation `g`
to F at `g + 2`, and preserves the signed label. Four glued roots swap
factors, and two pure roots in the destination amplitude factor implement
the spin-axis exchange `i → i + 2`. A bare factor swap has zero
gapped-to-gapped restriction in the common frame. With parity the restriction
is `WallExchange.back`; the upper-right adjoint link is
`CyclicSeesaw.cyc y ⊗ I₈`. The direct light-to-light crossing is zero.

For nonzero `y`, the zero-energy Schur mass factors into one generation-space
matrix per signed label (`occupied_light_mass`). Excluding the static vacancy
from the light input leaves every active-neutrino row zero while retaining
its signed index in the gapped block. Each of the three active-neutrino
light vectors lifts to an exact zero mode of the full zero-momentum
Hamiltonian (`neutral_exact_zero`). Each occupied label has its own two
generation-space flip matrices, with the same inverse link between them.
The coherent control and the flip coefficients are tracked in REVIEW.
The class-blind
flip disturbs the other wall's labels uniformly and mixes lepton and colour
labels in classes `v` and `c` (`tools/label_flip_check.py`).

With both light banks included, `paired_light_mass` gives the full
label-wise Schur mass at zero energy. Its neutral block is
`B₀ · cycInv(y) · A₀ᴴ` (`neutral_paired_mass_entry`), where `A₀` and `B₀`
are the static and active neutral flips. In the vacancy-truncated model
`A₀` is set to zero. Admitting and deriving the neutral flips and their
generation dependence is separate from identifying the crossing partner.

For diagonal on-site flips `A₀ = diag(a)`, `B₀ = diag(b)`, the neutral
block is a reverse cycle. Its only entry in row `g` is at column `g + 1`
with weight `b_g · y_g⁻¹ · conj(a_{g+1})`. The Gram matrix is diagonal
with the squared moduli of these weights
(`diagonal_neutral_mass_entry`, `diagonal_neutral_gram`).
With common magnitudes on each of the two flip families and on the
crossing, the Gram matrix is scalar for every assignment of phases
(`diagonal_neutral_gram_uniform`). The diagonal-flip Schur mechanism
therefore needs unequal effective weight magnitudes to split the
neutral masses.

### Static vacancy and neutral light modes

`VacancyProjection.invisible_line` identifies the kernel of the absolute
packet hypercharge generator on arbitrary coherent superpositions. It is
one line, the inventory's static sterile slot. Its orthogonal complement is
the generator's range (`occupied_fixed_iff`), and the weak and colour
updates preserve that sector (`gauge_updates_preserve`). This uses the
existing packet representation. Relative phase to the reference is a
different readout (`PMConstants.SectorCapabilities.sterile_has_relative_phase`).

`staticLight_agrees` transports the occupied projection to the
static wall in each generation. Applying it to the output of the
label-preserving static flip gives precisely `staticFlip`
(`projected_static_flip`). The pure static-vacancy light vectors are
stationary and the rest generator has no source into them. The projection
retains the signed label in the gapped block, and the three active
neutrino light vectors still lift to exact zero modes when the crossing
is invertible (`neutral_zero_after_projection`).

`VacancyPreparation` constructs a finite preparation using the existing
absolute packet hypercharge transport and two-port coherent comparison.
At the supplied phase step `6π/5`, the sterile slot is fixed and every
occupied slot has a nontrivial fifth-root phase. Retaining the minus branch
at the first four positive multiples of that step gives exactly
`(5/16) · occupied` (`filter_eq_projector`). Each comparison has a
unitary dilation. The retained branch has the occupied sector as its
range and carries `25/256` of the squared norm of the occupied input.
The native firing of these phase gates and routing of the retained
branch to the static light wall still require an update law. The
construction projects the existing neutral-degenerate Hamiltonian.

## Protocol readout

Numerical, `tools/protocol_readout_scan.py`. On the derived wire (`PMAction.ReferenceClassHop`: reference wall `κ_R = (K, k, k)`; `PMAction.CarrierAdmittance`: other wall class-blind, `κ_O = (K, K, K)`; `K = 1`) the cycle resonance is `δ³ = −1` (`PMAction.OtherWallStationary`). At every cube root the bare wire has `m₁ = 0` and `m₂/m₃ = √(3/2) k`: `0.0045` for `k = α/2`, `0.0089` for `k = α`, the same for every protocol. The data (`m_μ/m_τ = 0.0595`, `m_s/m_b ≈ 0.019–0.022`, `m_c/m_t ≈ 0.0036–0.0042`) then need a weight `s` on the heavy label (both walls) per protocol: `s_e : s_d : s_u ≈ 1 : 2.7–3.2 : 12–13.5` for `α/2` (`1 : 2.6–3.1 : 9.6–10.6` for `α`), ordered by charge; the heavy label's mass scales as `s²`. The lazy flip law squares the bare ratio (`2·10⁻⁵`), far below every protocol, so the data favour the coherent event. CKM on the derived wire (weights as fitted): same root `|V_us| ≈ 0.0001`, `|V_cb| ≈ 0.009`, `|V_ub| ≈ 0.008`; different roots `|V_us| = √3/2 ≈ 0.866`, `|V_cb| ≈ 0.010`, `|V_ub| ≈ 0.011` (data `0.225`, `0.041`, `0.0037`): the bare wire's rotation is not the CKM. Mixing tests on the derived wire (`tools/mixing_candidates_check.py`, masses held at data): `|V_us| = 0.225` is reached by a relative flip phase, a light-class asymmetry, or an other-wall cycle phase or asymmetry, so it does not discriminate; `|V_cb|` stays at `0.002–0.010` under every deformation tried (those, the weight on one or both walls, a joint fit, `k/K` from `α/4` to `10α`), with `|V_cb| ≈ |V_ub|`. So the wire's mass matrices cannot give `|V_cb|`; PMFlavor's transfer readout does (`PMFlavor.ReferenceRouting`). Charge-weight test: one `a` in `s ∝ e^{a Y_R}` gives down and up `0.82` and `0.77` (PDG mixed scales), `0.74` and `0.75` (`m_b`, `m_t` at their own scale), 2–11% apart across quark-mass choices (`k = α/2`; `7–18%` at `k = α`). Lightest masses: a real offset `δ = −1 + ε` off the resonance reproduces each `m₁/m₂` with `ε ≈ 0.038 (e), 0.14 (d), 0.0024 (u)`, keeping `m₂/m₃` within 2–7%; with those offsets the same-root CKM is `|V_us| ≈ 0.063`, `|V_cb| ≈ 0.007`, `|V_ub| ≈ 0.0065`.

### Lifting the resonant zero

`ResonanceLift` gives the other-wall determinant for three independent
on-site detunings: `d₀d₁d₂ + κ₀κ₁κ₂`. Multiplying the bare resonant wire
by dressing matrices preserves the zero determinant. At a fixed nonzero
resonance, adding an offset `ε` to any single diagonal flip leg changes
the other-wall determinant to `δ² ε`. In the two-wall Hamiltonian with
invertible crossing and reference flip, the full zero mode survives
exactly when `ε = 0` (`shifted_full_zero_iff`). The charged Schur mass
determinant also includes the reference-to-crossing factor
`det(R)/det(Y)` (`shifted_schur_det`).

If a protocol can independently vary the common detuning, a fixed
additive perturbation can be retuned to zero (`retuning_exists`). For a
real single-leg offset and a positive cycle product, the retuned value
can always be chosen strictly negative (`negative_retuning_exists`).
Conversely, distinct single-leg offsets at a shared detuning and cycle
product cannot both stay resonant. The physical calculation must derive
both the register insertion and the constraint on the common detuning.

The uniform-offset diagnostic above uses `δ + t` on all three legs.
`det_shifted_eq_uniform_iff` matches its determinant with one insertion
`ε = ((δ + t)³ − δ³)/δ²`, independent of the chosen leg or cycle.
At `δ = −1` the formula is `3t − 3t² + t³`. For the recorded offsets
the matching insertions are about `0.110` (e), `0.364` (d), and
`0.00718` (u). In the unweighted wall, with `z = 1 − t`, the local
insertion raises the sum of squared singular values by
`(z² − 1)²(z² + 2)` (`det_matched_trace_gap`).
The [weighted scan](../../tools/protocol_readout_scan.py) also changes
the ratios on the static vector leg. For example, the down diagnostic
changes `m₁/m₂` from `0.05034` to `0.04393` at equal determinant.
These are comparisons using the earlier wire inputs.

### Charged insertion on the static wall

At the packet hypercharge step `3π/4`, the static vacancy and the electron,
up and down channels have eigenphases `1, i, −1, −i`, respectively.
`ChargedInsertion.select_static` gives the exact projection onto each
static sector as two phase-matched plus-port comparisons, first with the
target-corrected transport and then with its square. The matching channel
has amplitude one. The projection is constant across the three colours.
`joint_selector` combines this comparison with the glue-class test.
The vector class occurs on the static wall at generation index `2`, so a
conditional coherent flip there adds one diagonal leg to the selected
protocol's generation matrix. The index is a coordinate of the glued
encoding.

With nonzero extra amplitude and a common bare resonant detuning,
`full_zero_iff_unselected` removes the selected sector's exact zero mode
in the full two-wall Hamiltonian, with invertible crossing and reference
flip. If an unmodified calibration channel stays stationary under the
same real detuning, `calibrated_detuning` pins it to the negative cube
root of the positive cycle product. The channel selectors specify
where a conditional pulse acts. The native law that admits and fires it,
its pulse area, and the existence of a shared stationary calibration
remain open.

### Protocol Toll constraints

`ProtocolToll` derives four colour orbits on the active packet from its finite
relabelings. Any reversible colour-equivariant map on the labels preserves
the coloured and colourless sectors. A fixed word of weak and colour
relabelings charges weak partners equally when each operation charges its own
price on a changed label (`eventToll_weak_partners`). The proof uses the
commutation of the relabelings with the weak involution. An even reading also
ties the partners. For the comparison order `ν < e < d < u`, Lean excludes
every monotone function of a single odd scalar reading and every positive
sector factor times a sign factor.

The product of two linear overlaps with fixed references is even under the
weak toggle. Both transported labels change sign
(`overlap_product_weak_partners`). Keeping the full signed pair of overlaps
with the fixed vector `+2e₀` still gives a collision between the neutrino
and one up colour and between the electron and the corresponding down
colour on the heavy generation's two walls
(`heavy_reference_overlap_collisions`). Those inputs cannot give a strict
four-species ladder under any scalar postprocessing.

The proposed label-only chain uses a coloured-to-colourless transition, so a
reversible colour-equivariant update on the labels cannot realize it. The
unrestricted forward root-displacement graph in the vector frame also has
shortcuts (`forward_shortcuts`): every active down or electron label can
reach an up label in one displacement, and every up label can reach the
active neutrino in one. Here forward means nonnegative component on the
reference axis. These exclusions use the substrate operations and the
comparison order, with no mass values in the proof.

Comparison diagnostics are in `tools/toll_forms_check.py` and
`tools/readout_placement_check.py`. In the wire fit with `k = α/2`, the
four inferred weights are about `0.030, 0.087, 0.26, 1.14` for `ν, e, d, u`.
The neutrino target assumes a neutral mass mechanism. The fitted ladder
has a typical step factor `3.2–3.4` and also appears when only the
reference wall is weighted. Weighting only the other wall or scaling the
detuning reaches the up comparison alone in the scans. A passive node load
lowers the bare coupling (`PMAction.ReferenceNodeBoundary`), while the
charged-lepton and down comparisons need a larger effective coupling.
These are targets for a future substrate calculation of the flip coefficients.

The static hypercharge comparison gives another exact test. Take the
unchanged reference branch in `PMAction.CommonResponse` and use the
packet hypercharge transport for the other branch. The vacancy has zero
flag probability. The absolute hypercharges of down, up and electron
are in the ratio `1:2:3`. Their flag probabilities obey
`P_e + 3P_d − 2P_u = 4P_d(1 − 2P_d)² ≥ 0` at every phase
(`ProtocolToll.hyperchargeFlag_static_gap`). Every finite nonnegative
weighted sum of those flags with a common baseline therefore satisfies
`2(T_u − T_ν) ≤ (T_e − T_ν) + 3(T_d − T_ν)`
(`hyperchargeFlag_schedule_bound`).

For a common positive affine map from that Toll to the wire amplitude,
the same bound holds for the amplitudes. With a nonnegative baseline
and `s_e < s_d` it requires `s_u < 2s_d`. The nominal charged
comparison has `s_u/s_d ≈ 4.38`. An affine map to squared amplitude
likewise requires `s_u² < 2s_d²`. These tests use the charged order and
do not require a neutrino mass prediction.

The generic comparison, repair cost, and conversion from a scheduled
pulse to its wire coupling belong to PMAction. The evaluation on the
E8 protocol packet, and the test against the heavy-weight readout,
belong here. This bound covers common per-flag pricing against an
unchanged reference. A label-conditioned repair length or a joint
reference response requires its own derivation.

The conversion itself is derived in `PMAction.TollAmplitude`: a label with
Toll `T` keeps amplitude `exp(−T/2)`, which is not affine. Under it the
static flags are not bounded this way. At the steps `π/2` and `3π/2` the
electron, down and up flags are `(1, ¼, ¾)` and `(1, 1, 0)`
(`flags_quarter`, `flags_three_quarter`). Counts `w₁, w₂` give
`T_e − T_d = ¾w₁` and `T_d − T_u = w₂ − ½w₁` (`survivalToll_differences`),
the strict order `s_e < s_d < s_u` for `w₁ > 0`, `w₂ > ½w₁`
(`survival_ladder`), and `2s_d ≤ s_u` exactly when `w₂ − ½w₁ ≥ 2 log 2`
(`doubling_iff`). The steps are a witness, not a derived schedule.

One step at a time: a static step is fixed by its down flag `d`. The up
flag is `4d(1 − d)` and the electron flag `d(3 − 4d)²`, so the step adds
`8d(1 − d)(1 − 2d)` to `T_e − T_d` (positive only for `d < ½`) and
`d(4d − 3)` to `T_d − T_u` (positive only for `d > ¾`)
(`step_differences`, `step_orders_lepton`, `step_orders_quark`). No
single step orders the charged labels (`single_step_no_order`). Their
sum `16d(d − d₋)(d − d₊)`, `d∓ = (5 ∓ √5)/8`, is not positive inside
`[d₋, d₊]` (`step_charged_span`, `window_no_span`), so a schedule inside
that window gives `T_e ≤ T_u` (`window_no_ladder`). The vacancy
preparation's steps `k · 6π/5` sit exactly on the window's ends
(`fifth_root_steps`), and the charged selector's step `3π/4` has `d = ½`
(`selector_step`, `selector_in_window`).

Doublet-position readouts. A weak gate that treats the partners
differently must export the doublet position
(`RefreshMap.asymmetric_gate_records`). A static step with down flag `1`
flags down and the electron fully and up and the vacancy not at all: it
reads that bit on every static label (`full_readout`; step `3π/2`). It
adds only to `T_d − T_u`. The electron flag is `1` exactly when the down
flag is `1` or `¼` (`lepton_readout_iff`); the second is the lepton-only
readout at `π/2`, below the window (`quarter_below_window`), adding `¾`
to `T_e − T_d` and `−½` to `T_d − T_u`. These are exactly the witness
steps of `survival_ladder`.

What one charged-current event requires (`EventRequirements`). The
emitted labels depend on the parent's sign alone (`pairs_of_sign`,
`pairs_disjoint`), and no axis-only rule can choose them
(`axis_cannot_choose`): the event requires exactly the parent's doublet
bit. The quark bit is read only by the full readout (`quark_bit_iff`).
If each label pays only its own event's readout, electron and down pay
`1` and up and the vacancy `0` (`own_event_tolls`): own-event accounting
ties `e` with `d` and `u` with `ν`. An ordering needs flags a label
receives in other labels' events.

A persisting massive label is on both walls with equal weight
(`PMAction.WallRestChirality.charged_weight_half`), so its flag is the
mean of its active and static slots (`massive_flag`; the readout does not
interfere channels, `PMAction.DiagonalReadout.state_flag`). The active
doublet slot cannot read the doublet bit. The full readout `3π/2` reads
both the lepton and the quark bit (`full_reads_both`) and gives massive
flags `¾` (electron, down) and `¼` (up, vacancy) (`full_massive`). So
the doublet readouts, with Economy and both walls, separate up from down
and never the electron from down. These Tolls are generation-blind, and a
generation-blind Toll scales the wire mass by one factor and cancels from
every ratio (`uniform_weight_cancels`); only a Toll that reaches some
generations' flips matters. The light generations pass through the
reference node and the heavy one does not (`PMAction.ReferenceClassHop`);
a Toll on the node legs raises the effective heavy weight by `exp(T/2)`
(`node_toll_raises_heavy`).

### Finite control of the direct heavy flip

`HeavyFlipControl` uses the generation address and the glued carrier frame.
The direct insertion on the reference wall avoids class zero at both ends
exactly for generation zero (`direct_iff`, from
`ReferenceClassHop.touches_reference_class`). A bare glued root cannot
supply this address (`no_root_only_direct_address`). In the addressed
direct-flip model, the forward endpoint exchange is the existing
swap/triality word (`flip_encoded`). The reverse direction uses its
inverse on the paired endpoints. The added control leaves the light node
paths unchanged (`flip_light`).

The transported label supplies a sector bit (reference axis versus colour)
and a sign bit (doublet position). The record is colour-invariant and
survives the wall exchange (`record_colour`, `record_opposite`). A clean
two-bit bank receives the code by conditional exchanges (`write_clean`).
`IndependentRegisters` and `RegisterControl` execute the write and the
selected endpoint exchange as a reversible word on the occupied banks
(`registered_word`). A supplied phase on a record block is unitary on
the full configuration space (`registered_phase_unitary`). For flip `F`,
the phase has exchange coefficient `(1−z)/2` on its two endpoints and
acts as identity on fixed points. This uses
the available encoded endpoints and supplied joint controls. Native bank
preparation, firing and timing remain open.

`CompanionHeavyFlip.ready_pack` supplies the generation address from the
other occupied glue class on a retained companion carrier. The ordered
live/companion classes select the incoming heavy wall for every companion
index. The guarded endpoint word also updates the companion: its class
becomes the vacated live class, with its carrier index retained
(`run_pack`). Both directions agree with the finite control, and light
inputs are fixed. Running the word twice restores the packed state
(`run_twice_pack`). This identifies the required initial class and the
return rule. A native source for the companion and admission of the joint
update remain open.

With the label retained as a control, the species blocks are already
orthogonal. If a gate instead sends distinct inputs to overlapping
wire outputs, reversibility of the product with an exported record forces
orthogonal records (`CoherentGate.tensor_dot`). The weak-pair version
applies when the two output columns have nonzero overlap
(`unequal_needs_orthogonal`). The two-bit code suffices for all four
species when the output no longer carries the distinction.

### Record comparisons and heavy-flip Toll

`HeavyFlipRecords.quark_auxiliary_gap` excludes a shared auxiliary-only
readout driven solely by diagonal packet hypercharge on the massive state.
For any comparison schedule and auxiliary decoder in this class, the
probability of an auxiliary outcome is the mean of its two slot
probabilities. The active up and down slots have equal charge, so every
outcome-probability gap is at most `½`. Orthogonal auxiliary records
would allow an outcome with probabilities 1 and 0. This exclusion allows
arbitrary comparison steps, repetitions and auxiliary postprocessing
with the same preparation, provided the system slots are left in place
and no other label information enters the control. A separate check
(`electron_down_overlap`) gives squared branch overlaps `1` at `3π/2`
and `¼` at `π/2` for electron and down on either fixed wall. Independent
copies of these two comparisons therefore cannot write the sector
distinction for those labels even on a single wall.

The comparison flags still give exact additive prices if these visits
are supplied. The full comparison fills the shared **static** doublet
requirement in one visit. Economy gives the following both-wall mean
flags (`full_only_minimum`, `quarter_massive`, `paired_minimum`,
`paired_tolls`).

| Required comparisons | Electron | Down | Up | Neutral pair |
| --- | ---: | ---: | ---: | ---: |
| Full `3π/2` | `¾` | `¾` | `¼` | `¼` |
| Lepton-only `π/2` | `¾` | `(3−√3)/8` | `(5−√3)/8` | `¼` |
| One of each, if both are independently required | `3/2` | `(9−√3)/8` | `(7−√3)/8` | `½` |

The full visit ties electron with down. The paired flag budget gives
`s_e < s_d < s_u` through `exp(−T/2)` (`paired_ladder`), but the
comparisons fail the record test above. Its gap ratio is
`2/(3+√3) ≈ 0.423` (`paired_gap_ratio`).

An exact conditional writer uses two diagonal phase comparisons in the
transported carrier frame. The phase is `π` on the marked carriers and
zero elsewhere for each predicate: reference axis and negative position.
With a clean auxiliary branch, `(1 ± exp(iφ))/2` routes it to the
corresponding record bit. The code is the same on the two walls
(`orbit_bit_price`). With these phase controls admitted and the two bits
required separately, one visit per bit attains the Economy Toll
(`orbit_record_minimum`). The flag Tolls for the stated polarity are
`(2,1,0,1)`, and the charged weights are
`(exp(−1), exp(−½), 1)` (`orbit_record_tolls`, `orbit_record_ladder`).
These are expected registration counts for the comparison visits. They
exclude the scheduled primitive pulse and preparation prices, which need
their own accounting. The finite gate does not select the phase coupling,
the bank preparation, the polarity as a physical charge convention, or
the event that fires it.

Comparison only. The exact-bit candidate has gap ratio 1 and the paired
hypercharge budget has ratio about 0.423. The mass-scale diagnostics in
`tools/heavy_toll_targets.py` require about 1.1–1.5.

### An electric-charge record on both walls

`ElectricHeavyRecord.electric_generator` identifies the packet’s unbroken
`Q = T₃ + Y/2` as the diagonal generator for both comparisons. Its charge in
the transported frame is `(2/3)·[colour] − [negative position]`
(`charge_from_bits`). A comparison against the neutral phase at `3π`
reads the parity of `3Q`, hence the position. The second comparison uses
the recorded position to select a same-position reference. The
lepton–quark contrast has magnitude `2/3`, so `3π/2` resolves the
sector exactly. These are the least nonnegative times in the two
specified comparisons (`position_time_minimal`, `sector_time_minimal`).
Both charges are preserved across the glued wall pairing
(`same_wall_pair`). The two comparisons give the required complex
kick signs (`packet_kick_phases`).

The moved orbit of an actual root supplies the two branch states. A
quarter pulse from its clean basis seed prepares balanced populations.
After the conditional electric kick on the second branch, three
forward quarter-times of the same root complete the inverse.
`root_writer` gives the resulting basis record, including the `−i`
phase on a marked record. The branch construction works on each
carrier class. The joint branch/payload coupling, the bank allocation
and its clean seeds still need a substrate implementation.

A colour phase reference gives the bit Tolls `(2,1,0,1)` in order
`e,d,u,ν`. A lepton phase reference with complemented sector decoding
reads the same information with Tolls `(1,2,1,0)`
(`colour_reference_toll`, `lepton_reference_toll`).
The required phase resolution alone leaves this choice open.
There is also a distinct factor-flag ledger for the exhibited circuit
(`embedded_step_flag`, `pulse_flags`). Each branch preparation and
recombination contributes `¼`. The central signed kick contributes
half of its final record flag. With one registration per factor flag,
the two writers have Toll `1 + T_bits/2` (`two_bit_factor_toll`),
or `(2, 3/2, 1, 3/2)` for the colour reference. This counts the
three factor flags of each forward writer. Export, reset,
synchronization and a microscopic tariff remain separate obligations.


### Primitive crossing activity and clock limits

`HeavyCrossingCost` checks the six-reflection word and its reverse on
the two heavy-wall endpoints. For every signed label and either incoming
wall, the eight amplitude inputs give 48 steps. There are 27 fixed
steps, 20 unit-root steps and one twice-root jump
(`activity_histogram`). A separate tariff for either displacement length,
under uniform amplitudes, therefore gives the common price
`(20 c₁ + c₂)/8` (`uniform_cost`). Pricing the twice-root jump as
one elementary displacement requires an additional premise.
The complete step profiles pair under simultaneous reversal of both
carrier signs. Thus any profile tariff with antipodally paired amplitude
weights ties the two doublet positions on either wall (`sign_tie`).

`HeavyFlipNativeBoundary` shows that a fixed matched lattice probe is
orientation-blind at modulo-two resolution, and the actual in-band
read/undo tariff is invariant when its input is negated. Both heavy
walls also alias light-wall inputs in the untagged glued root encoding.
Consequently no untagged map can exchange the heavy pair on either
incoming wall and leave all light legs alone. A shared clean ancillary
seed leaves that collision intact. Preparing a clean record from
every wire and record input by a reversible closed update is excluded
(`no_closed_cleaning`).

For a supplied generation address and ready record, the closed
single-control clock family has the same 43-tick period for every
mask. A boundary toggles the addressed endpoint from either wall.
The idle mask yields zero endpoint moves and the excursion mask yields
two (`tick_event_iff`, `idle_and_excursion_counts`). The full turn
always restores the endpoint (`cycle_closes`). The excursion gives
one toggle in each direction per turn. The clock's closure permits
both schedules. In the physical wire, the equal-class gapped crossing
changes generation (`GappedGluedCrossing.equalClass_iff`), and the
on-site insertions in the two Schur mass factors are separate
operations. Endpoint exchange and the read/undo clock therefore leave
the placement and firing of the two physical insertions open.


### Other heavy-weight diagnostics

- **Half-period cadence.** Over the common static period `3π`, the
  lepton readout visits at `π/2`, `3π/2`, and `5π/2`. The quark
  visit is at `3π/2`. Merging the shared visit ties down with up.
  Counting coincident visits separately gives a Toll-gap ratio of
  `2/3`. A Toll proportional to the signed static hypercharge has
  gap ratio `3/2`.
- **Node leg.** Comparing the crossing label's hypercharge against the
  lepton-doublet reference on both walls gives `T_e < T_d < T_u`.
  Node-path damping raises the effective heavy weight
  (`node_toll_raises_heavy`). The gap ratio
  `(T_u − T_d)/(T_d − T_e)` is about 6 at small steps, 4.5 at
  `t = 1`, and 2.7 at `π/2`.
- **Bare-wire detuning.** The numerical check
  `tools/detuning_bound_check.py` gives `m₂/m₃ ≤ √(3/2) k` over
  complex detunings, with equality at the cube roots of the resonance
  condition. For `k = α/2` the maximum is about `0.00447`.
  At resonance, the inferred heavy weights are roughly `0.09` for
  electron, `0.26` for down, and `0.7–1.2` for up across the
  compared quark-mass conventions. These are comparison targets.

## Refresh map and weak gate

`RefreshMap.minimal` and `occupied_count` show that retaining the base protocol and active flag gives the coarsest deterministic description of weak refresh that preserves the inventory readout. Eight classes occur, including the vacancy. Colour permutations preserve each class and two refreshes restore each channel. At a canonical hypercharge maintenance visit, the addressed payload row exchanges its live discrepancy with its incoming record (`payload_visit`). Equality of next live bits for every incoming record array is equivalent to equality of channel addresses (`same_payload_readout_iff`). Even two active bulk channels of the same protocol can be distinguished this way (`routing_misses_payload`). With ledger arrays transported together, initially clean records and one designated channel marked in the incoming live array, `marked_payload_return` gives clean outputs through visit N on an orbit of least period N. At visit N+1 only the marked address reads true. On a nonreturning orbit `marked_payload_open` gives clean outputs at every positive visit.

For the candidate that consults a fixed bit array at the incoming address and applies one weak flip on true, `feedback_changes_iff` identifies the changed protocol labels. `feedback_injective_iff` proves that reversibility on channel labels requires and suffices for equality of the bits on each weak pair. A single active mark produces a collision (`single_active_collision`). For one addressed maintenance swap followed by routing on the returned live bit, clear incoming live payloads suffice to recover the incoming channel and entire ledger (`recover_visit_channel`, `visitRoute_clean_injective`). The record bits may be occupied. On unrestricted inputs even the complete outgoing ledger can coincide for two weak partners (`visitRoute_collision`). For consecutive visits without intervening transport, `pairVisit_exact` projects a moving channel onto its weak pair. Starting with clear live bits, the fifth pair state equals the first. At any known visit count the pair state identifies the initial position and both initial record bits (`pair_clean_recover`). A fixed channel restores its entire ledger after two visits (`fixed_visit_twice`).

The Map's clean requirement is exact. Recovery after one visit needs only the partner row's live bit clear (`recover_partner_clean`), so the visit with routing is reversible on every input whose eight active payload rows are clear, with static rows unrestricted (`visitRoute_active_clean_injective`); one occupied active row already gives a collision (`visitRoute_collision`). A gate that reads different bits on two weak partners collides them on the channel, so any reversible extension must export a record separating the partners, that is, the doublet position (`asymmetric_gate_records`). The weak flip moves exactly the active channels (`moves_iff_active`).

`CoherentGate` is the coherent version on one weak pair. Gating the two partners at angles `a` and `b` gives output columns with overlap `sin (a − b)` (`cross`), so the gate is reversible exactly when the angles agree up to a half turn (`columns_orthogonal_iff`). With records written beside the outputs the overlap is `sin (a − b) · ⟨r₀, r₁⟩` (`recorded_orthogonal_iff`): a nonzero wire overlap requires orthogonal records, supplying one full bit of doublet position per event (`unequal_needs_orthogonal`).

`streamRoute` tests a different coupling: the common ledger stream advances independently and its new live bit controls the channel after each tick. Clean payload readouts preserve every channel (`streamRoute_clean`). With the single-address preparation on an orbit of least period N, the complete route at tick N+1 equals the single-address gate (`streamRoute_first_return`). An active mark therefore merges two routes with identical outgoing streams.

With inventory channels carried as configuration values, the native port update exports the entering channel exactly. `native_route_iff` characterizes when it realizes a proposed conditional weak route: the incoming record must already contain the target. `native_outputs_distinct` separates distinct incoming labels on the outgoing record. A single common target fails across the inventory (`no_common_target`). The repair root preserves doublet position on its vector-carrier addresses (`repair_root_preserves_position`). A table supplying literal targets needs at least twelve slots, one per weak orbit (`target_table_bound`). On a connected stationary native background even arbitrary site and port selection gives only two port values (`stationary_source_insufficient`). An orbit index and one position bit identify each channel; feedback preserves the orbit and toggles that bit exactly on a marked active channel (`feedback_position`).

`RefreshMap.gated_word_matches` identifies the conditional weak toggle on all channels with the antipodal carrier Weyl word on the active bank and identity on the static bank. If a common clock mask-change bit gates that word, `clockRoute_endpoints` reduces the entire route to the initial and final mask values; `clockRoute_closes` restores every input channel over a full clock cycle. This coupling uses a supplied mask and word-level gate.

## Selected E8 decay checks

Frozen comparison values live outside the theorem tree.  The elementary-particle
(electron/muon/tau) checks are:

| decay | E8 model | comparison | status |
|---|---:|---:|---|
| μ → e ν ν̄ | 2.196987–2.196998×10⁻⁶ s | 2.1969811(22)×10⁻⁶ s | E8 inputs, derived phase space, supplied one-loop factor (`MuonLifetimeCorrected`) |
| τ → e ν ν̄ | ≈2.9×10⁻¹³ s | 2.90×10⁻¹³ s | E8 masses + supplied `B_e` |

The nucleon and meson decay checks (n, π, K, π⁰) are hadron-level and live in
[`PMHadrons/OVERVIEW.md`](../PMHadrons/OVERVIEW.md).

The structural channel/status ledgers are in `ChannelParticleLedger`,
`TierLedger` and `ChannelStatusLedger`.  SM particle names in the comparison
ledgers are labels; the substrate objects are protocols, tiers and cohorts.

## Amplitude, rate and width

| Modules | Checked result | Retained inputs |
| --- | --- | --- |
| `SpinorRateBridge` | Paper II's actual bilinear amplitude in Paper V's real-momentum convention: initial-spin-averaged square `64 G²(p·k̄)(p_e·k)` | V−A vertex, on-shell states, complete orthonormal kernel bases |
| `MuonAmplitude`, `MassiveMuon` | V−A trace algebra; the muon's mass cancels between chiral vertices (`chiral_sandwich`, `massive_trace`, `massive_amplitude`) | — |
| `MassiveExternalAmplitude` | Same `64 G²(p·k̄)(p_e·k)` for **arbitrary real masses** on all four legs (`spin_averaged`, `rate_input`) | Contact vertex, signed antiparticle convention |
| `WExchangeRate` | Contact amplitude as the `q→0` limit of tree `W` exchange; `G=√2g²/(8m_W²)`, `G=1/(√2v²)` (`exchange_rate_input`, `exchange_rate_fermi`, `bases_exist`) | That this exchange is the substrate interaction |
| `WeakMatching` | Mediator matching `M_W²=g²v²/4`, `G=1/(√2v²)`, normalized spectrum | Physical coupling/mediator |
| `TauE8` | `tauLifetimeE8 = τ_μ(m_μ/m_τ)^5 B_e`, positivity | supplied `B_e` |
| `CarrierCouplings` | `CarrierAmplitude`, `amplitude`, `CarrierTransition`, E8 `em/weak/strong` slots, `CarrierTransition.amplitude`, `carrierMatrixElement` (actual external-spinor contact amplitude), `CarrierExternalStates` / `matrixElement`, `CarrierSpinorState`, `OnShellExternalStates`, `OnShellExternalStates.matrixElement`, transition weight, `weakCoupling_eq_fermi` | amplitude model selection |
| `TierLedger` | `tiersFor` up `{0,2,3}` / down/lepton `{0,1,2}`, `massProvenance`, `decayProvenance`; tier subsets and provenance labels. |
| `TopTransition` | `Boson`, `topInitial`, `bottomFinal`, `topFinal`, `topT`, `topRate`, charge conservation. |
| `NeutrinoPropagation` | `TwoFlavour`, `phase`, `survival`, `transition`, bounds and sum rule. |
| `CarrierTransitionOperator` | `weakOf`, `carrierProductAmplitude`, `substrateOperator`, `substrateOperator_zero_of_not_decay`; muon/tau operator systems with `totalWidth = |T|²·phase`. |
| `SubstrateTransition` | general transition form `partialWidth = |⟨f|T|i⟩|²·Φ`, `totalWidth`, `lifetime`, `branching`; `singleChannel`; muon E8 width as an instance. |
| `ChannelStatusLedger` | `ChannelStatusRow`, `statusRowsFor`, `statusLedger`; channel × allowed-tier expansion with mass and decay provenance. |
| `ChannelParticleLedger` | `ChannelRow` (channel, index, base protocol, species, colour, chirality, anchor, charge), full 16-row `ledger`; `ledger_length`, `active_channels_card = 15`, `channelCharge_eq_Q`, `species_none_iff_sterile`. |
| `SubstrateFinalStates` | substrate-native `BaseProtocol` final states, `baseCharge`, `AdmissibleFinalState`, `betaMinus_admissible`; primary B1 ledger before SM comparison labels. |
| `FinalStateBridge` | `FinalStateChannel` with conserved `chargeSum`; `betaMinus`, `neutrinoFinal`, `finalState_charge_conserved`; first B1 final-state ledger. |
| `CarrierSpecies` | `CarrierSpecies`, `ofBaseProtocol`, `channelSpecies`, `CarrierSpecies.charge`, `channelSpecies_charge`, sterile/no-species lemmas; channel label → base protocol → species | mass/amplitude assignment |
| `RadiativeCorrection` | supplied `R`, `correctedRate`, `correctedLifetime`, positivity | derived radiative correction |
| `MuonLifetime` | E8-input muon width `G_F²m_μ⁵/(192π³)`, `muonLifetime`, positivity; `muonWidth_eq_integral` | finite spectral-channel phase space |
| `MuonRate` | `192π³` derived: `pair_kinematics`, `tensor_coeffs`, `two_body`, `electron_measure`, `rate_density`, `muon_rate = G_F²m⁵/(192π³)`, `spectrum_form` | `Φ₂=1/(8π)` and the electron measure/flux derived in `PolarMeasure` |
| `PolarMeasure` | the `ℝ³` momentum measure by spherical change of variables: `sphere_area_three`, `integral_radial_three`, `massless_lorentz_measure`, `two_body_phase_space`, `massShell_reduction`; `two_body_from_lebesgue` (`Φ₂ = 1/(8π)` as the energy-shell derivative of the cumulative pair integral over `ℝ³`) | — |
| `MassiveDaughterSpectrum` | Massive charged daughter, massless neutrino pair: `threshold`, `kinematics`, `radial_measure`, `pair_density`, `massless`, `rate_positive`, `width_scaling` | Contact vertex, transported pair average |
| `MassiveWidth` | Closed massive-daughter width `G²m⁵/(192π³)·[1−8r+8r³−r⁴−12r² log r]`; `closed_width`, `phase_zero/one/continuous`, `phase_positive`, `threshold_width` | Tree contact spectrum, normalizations |
| `MuonLifetimeCorrected` | `τ_μ = τ_tree/(f(r)·q)`: `r = (m_e/m_μ)²` (`r_bounds`), derived phase factor `f(r) = MassiveWidth.phase r` (`phase_bounds`, `0.99981295`), `α = 1/geometricIndex`, `corrected_bounds` `2.196987–2.196998 µs` (measured `2.1969811(22)`); e8p `muon_lifetime_s` | one-loop QED factor `q = 1 − (α/2π)(π² − 25/4)` (Kinoshita–Sirlin), supplied; higher orders (≈5 ppm) not included |
| `MuonQEDLoops` | The QED loop terms of muon decay at E8 inputs, in one place: the coupling at the muon scale `α_r⁻¹ = α⁻¹ − (2/3π) ln(m_μ/m_e) ≈ 135.90` (`log_muon_bounds`, `alphaR_div_pi_bounds`); one loop with its electron-mass terms (`dq1_bounds`); two loops `6.700 (α_r/π)²` (`dq2_bounds`); phase space `dq0` (derived) | the loop coefficients and running-coupling prescription (van Ritbergen–Stuart) |
| `MuonLifetimeHigherOrder` | `τ_μ = τ_tree/(1 + Δq⁽⁰⁾ + Δq⁽¹⁾ + Δq⁽²⁾)`: `lifetime_bounds` `2.196974–2.196984 µs` (measured `2.1969811(22)`; the one-loop row was `+5σ`) | via `MuonQEDLoops` |
| `TauLifetimeCorrected` | Tau lifetime from the measured `τ_μ` and supplied `B_e` with the electronic partial-width ratio corrected: phase space `f(x_μ)/f(x_τ)` (derived), `W` propagator (E8 `M_W`), one-loop QED at each lepton scale (`α(m_τ)⁻¹ = 133.3` supplied); `tau_lifetime_corrected` `291.03–291.06` fs (measured `290.3 ± 0.5`; tree `291.15–291.17`) | measured `τ_μ`, `B_e`, `α(m_τ)` |
| `MuonRadiativeLog` | The leading one-loop contact log in muon decay vanishes: `c = 0` for charges `(0, −1, −1, 0)` (`leptonic_no_log`) and in the charge-retention order, a conserved `e–μ` current (`retention_no_log`); the leading-log rate factor is one (`rate_factor_one`) | — |
| `PairInvariantSpectrum` | Uses the massive-daughter tree spectrum to derive the density in `q² = (p − p_e)²`, its physical interval `[0,(m − μ)²]`, and its weighted change of variable with Jacobian `1/(2m)`. The unweighted integral recovers `MassiveWidth.closed_width`. At `μ = 0`, the normalized invariant `z=q²/m²` gives the weight `2(1−z)²(1+2z)` | Tree contact spectrum with massless neutrinos |
| `RadiativeIntegrals` | Real dilogarithm series equals the integral of `−log(1 − x)/x` on `[0,1]` (`dilog_eq_integral`); `Li₂(1) = π²/6` from the Basel sum. The kernel is integrable at the endpoint and its reflected form `−log x/(1 − x)` has the same integral | — |
| `InclusiveMixing` | Unresolved orthogonal channels: `amplitude_weight`, `equal_kinematics` (sum = 1 for any unitary mixing; applied to the on-axis matrix in `PMFlavor.InclusiveWidth`), `kinematic_bounds` | Orthogonal final states, common kinematics |

### Inclusive one-loop muon benchmark

The [continuum certificate](../../tools/muon_radiative_certificate.py)
takes the massless inclusive `F₁(z)` kernel with `z = q²/m_μ²`, where
`q` is the sum of the two neutrino momenta even when a photon is emitted.
The Abelian version of the heavy-to-light result has normalized density
`F₀ − α/(2π) F₁`. The script integrates the polynomial-log and dilogarithm
terms as exact moments and checks the result by quadrature. The integral
of `F₁` is `π² − 25/4`, or `3.619604401089358`. It uses the published sum
of the virtual and real terms as its input.
[Kühn and Mirkes, Eq. (52)](https://arxiv.org/pdf/hep-ph/9301204#page=12) ·
[Czarnecki and Melnikov, Abelian mapping](https://arxiv.org/abs/hep-ph/0112264)

`RadiativeIntegrals.softAngular_average` evaluates the continuum soft
factor from the two external charged legs. In the muon rest frame the
angular average at electron speed `0 < β < 1` is
`log((1 + β)/(1 − β))/β − 2`. It multiplies the soft radial integral.
The regulated virtual and hard-emission terms are derived numerically
in `tools/muon_radiative_derivation.py` from the substrate's conserved
wall vertex (`PMAction.SpinorVertex`) with explicit regulators (a
Pauli–Villars photon, a photon mass and an electron mass). The total is
independent of each regulator and tends to the kernel above as
`m_e → 0`: at `m_e = 3·10⁻⁴` the derived `ΔΓ/Γ₀` in units of `α/4π` is
`−7.76176, −7.37098, −6.88717, −5.69915, −1.54393` at
`z = 0.1, 0.3, 0.5, 0.7, 0.9`, against `−7.76131, −7.37086, −6.88718,
−5.69929, −1.54503`. Formal verification is open (REVIEW).


## Pair tensor and continuum angular integral

| Modules | Checked result | Retained inputs |
| --- | --- | --- |
| `PairIsotropy` | Rest-frame pair moments from sign flips / axis swaps / unit length: vanishing first and off-diagonal moments, diagonal `Φ/3`; `rest_covariant`, `normalized_rest` | Volume `1/(8π)` |
| `PairTransport` | Concrete `axisAverage`; Lorentz transport `transported_tensor`, `frame_independent`; `boost_lorentz`, `boost_to`, `timelike_pair`; `muon_density`, `axis_muon_density` | `Φ=1/(8π)`, electron measure, flux |
| `ContinuumPair` | Iterated Lebesgue angular integral with reduced density `1/(32π²)`: `volume=1/(8π)`, `first_moment`, `second_moment`, linearity on continuous test functions, `pair_massless`, `pair_contraction`, `massive_density`; invariance under rotations about the polar axis (`average_rotate_polar`, any `f` periodic in `φ`) and under `z ↦ −z` (`average_reflect_polar`) | Angular parametrization/density specified, not substrate-derived |
| `MassivePair` | Rest-frame tensor of a pair with masses `m₁`, `m₂` from the angular symmetries (`massive_rest_tensor`), covariant form `Q²⟨k₁k₂⟩ = Φ(P²/3) g Q² + Φ(E₁E₂ − P²/3) q q` (`massive_rest_covariant`), `massless_limit`, `two_body_kinematics`, `shells` | — |
| `ElectronMeasure` | Massive daughter measure from `∫_{ℝ³}`: `∫ g(E) d³p/((2π)³2E) = (1/4π²)∫_μ^B √(E²−μ²) g(E) dE` (`massive_lorentz_measure`); the massive width is the Lebesgue integral of the flux-weighted pair part over the daughter momentum (`width_from_lebesgue`) | three-body factorization into daughter × pair, flux `1/(2m)` |
| `NullBoost` | Boost along an axis acting on a massless leg: `|k'| = γ(|k| + βk₀)` (`nrm_boost`), inverse (`boost_inv`), Jacobian `|k'|/|k|` (`det_J`, `boost_hasFDerivAt`); `d³k/|k|` is boost invariant (`measure_invariant`) and so is the two-leg measure as an iterated integral (`pair_invariant`) | — |
| `TauBranching` | `B(τ→eνν̄) = 1/(1 + f(r) + N_c h)`: leptonic ratio from the derived phase factor at the E8 masses (`phase_bounds`, `0.9724–0.9727`), `N_c = D − 1 = 3` (`colours_eq`); parton level `h = 1` gives `0.2010–0.2012` (`parton_level`); the supplied `0.1782` needs `h = 1.2129–1.2132` (`supplied_needs`). The [tau inventory](../PMHadrons/OVERVIEW.md#channel-inventory-and-interfaces) uses the derived ratio | inclusive hadronic factor `h` ([PMHadrons REVIEW](../PMHadrons/REVIEW-AND-NEXT.md)) |
| `PairShell` | Shell coordinates `(E, ν, φ)` for a massless pair at total momentum `b e₀`: `|k| = (E + b cos ν)/2`, `|k̄| = (E − b cos ν)/2` (`nrm_Ψ`, `nrm_Ψ_bar`), Jacobian `(sin ν/8)(E² − b² cos²ν)` (`det_J`, `Ψ_hasFDerivAt`), injective (`Ψ_injOn`), onto off a null half-plane (`Ψ_onto`, `image_ae_univ`); `∫ g d³k/(|k||P⃗−k|) = ∫_S (sin ν/2) g∘Ψ` for every `g` (`shell_integral`) | — |
| `PairSphere` | The pair tensor over the shell, computed: solid-angle moments `4π`, `0`, `(4π/3)δᵢⱼ` (`separable`, `mono_avg`); rest tensor `4π/12 g Q² + 4π/6 q q` (`rest_covariant`) and its boost by any Lorentz `Λ` (`transported`); the shell legs are the rest pair boosted to `q = (E, b, 0, 0)` (`leg_spatial`, `shellBoost_legs`, `shellBoost_rest`); `∫ k^μ k̄^ν dΩ*/(32π²) = Φ/12 g q² + Φ/6 q q`, `Φ = 1/(8π)` (`shell_tensor`, `shell_tensor_normalized`). With `shell_integral` this is the three-body factorization `pair_density` uses | — |
| `MassiveVolume` | Massive two-body volume: cumulative `(1/4π)∫₀^P r²/(E₁E₂)`, `dQ/dP = PQ/(E₁E₂)`, and an explicit inverse `momentumAt`. For any nonnegative pair masses, `shell_density_at_energy` proves the derivative of the energy cumulative above threshold, giving `(1/8π)(2P/Q)`. `massless_case` gives `2P/Q = 1` for two massless legs | — |

## Decay law, survival and routing

| Modules | Checked result | Retained inputs |
| --- | --- | --- |
| `Survival` | `survive=exp(−Γt)`, positivity, bounds, time constant, half-life | Exponential law |
| `DecayLaw` | Constant per-tick cost from Paper I survival (`ticks_exact`, `ticks_are_survive`), `hazard_pos_iff`, `compounded_limit` (finite→continuum); on the E8 tick `Δ = 43` a width `Γ` (in `m_e`) costs `ΓΔ` per tick and survival after `n` ticks is `exp(−Γ nΔ)` (`substrate_ticks`) | time homogeneity of the update; seconds via the `ħ/(m_e c²)` anchor |
| `Widths` | `lifetime=ħ/Γ`, rescaling, reference-width positivity | Width input |
| `Routing` | `Model` with latency descent and label preservation (recursive routing) | The routing model |

## Scaling bookkeeping and substrate bridge

| Modules | Checked result | Retained inputs |
| --- | --- | --- |
| `MassScaling` | Dimensional exponents `phaseSpaceExponent`, `kinematicDimension`; `three_body_dimensions`; spectrum polynomial | Stipulated contact interaction |
| `ScalingObligations` | Each of the three `M⁵` scaling relations from a derived homogeneity of an actual formula (`momentum_linear`, `dispersion`, …) | The formulas |
| `SubstrateBridge` | `conditional_exponent`: the three scaling relations force the fifth power for `D=4`; E8-internal independence witness; distinct positive cubic/quintic laws | The three relations are proof *inputs* |

## Particles, masses and charges (recorded as tensions)

| Modules | Checked result |
| --- | --- |
| `ChargeProtocols` | Charges from Paper III packets; `thirds`; `integer_iff_colourless` |
| `LeptonMasses` | `m_μ`, `m_τ` written in canonical E8 invariants and decomposed into named tier costs (`muon_ledger`, `tau_ledger`; the `π⁺` ledger is in `PMHadrons.MesonMasses`); muon feedback derived as a recursive fixed point (`muonFeedback_fixpoint`); E8-only enclosures (measured tensions in `tools/e8p/E8PConstants/PMElementaryParticles/LeptonMassPulls.lean`) |
| `QuarkMasses` | Six quark formulas written in canonical E8 invariants and decomposed into named tier costs (`up_ledger`…`top_ledger`); E8-only enclosures (measured pulls in `tools/e8p/E8PConstants/PMElementaryParticles/QuarkMassPulls.lean`) |
| `NeutrinoContext` | Contextual neutrino masses excluded by oscillation data (`weak_minus_rest_excluded`, `no_moderate_gap_ratio`) |
| `TauLifetime` | `τ_τ = τ_μ (m_μ/m_τ)⁵ B_e` (`rate_ratio`, `tau_lifetime_tree`); measured pull in `tools/e8p/E8PConstants/PMElementaryParticles/TauLifetimePulls.lean` |

## Species masses over the wire

The wire is `PMFlavor`/`PMAction`'s generation sector: with no detuning on the reference's wall
(`PMAction.ReferenceDetuning`) the light mass is `M = D_R (δ_O + cyc κ_O)`
(`PMAction.ReferenceWallMass`): one generation with a vector-class carrier (in-cycle, `K = 1`), two
with spinor-class carriers through the reference node (`k/K = α/2`, `PMAction.NodeAmplitude`), and
the other wall's detuning `δ_O`, which must be nonzero (`PMAction.UndetunedWall`). The wire is blind
to the species it carries in the bare model. Closure gives one crossing price in the absence of
an internal signal distinction (`PMConstants.HandoffAdmittance.closure_one_price`), and the
`D₄` geometry with the reference's axis cannot tell up from down
(`PMElementaryParticles.DoubletReflection`). So the wire fixes the form; species are protocols over it, and what
each protocol occupies is open (REVIEW). Earlier per-species scans fitted measured mass ratios and
CKM magnitudes; they were removed as Standard-Model fitting, not substrate results (in git history:
`tools/node_carrier_scan.py`, `tools/reference_wall_mixing_scan.py`, `tools/composite_mass_scan.py`).

## Final channels of a charged-current event

`FinalChannels`: on the register's label (vector frame: axis `0` lepton, `1..3` colour; sign the
doublet) the weak event is the antipode, same axis and opposite sign (`GluedRegister.neg_class`), and
on the wire mode it is the native charged current (`PMAction.NativeExternal.native_current`). The flip
changes the charge by exactly one unit on every label (`flip_charge`). A charged-current event takes
the parent `x` to `flip x` and emits `y` with the antilabel of `flip y`; charge is conserved exactly when
`y` has the parent's sign (`pair_conserves_iff`). So there are four emitted pairs, one leptonic and
three coloured (`pairs_card`, `colour_pairs_card`, `lepton_pair`); for a down lepton parent they are
`e ν̄` and `d ū` per colour (`down_lepton_pairs`). This is the channel count of
`TauBranching.branching` (`1` per open lepton pair, `N_c = 3`), now from the label. Which pairs are
open is kinematic (PMHadrons for quark pairs); generation changes at the vertex are PMFlavor's.

## External states

`ExternalStates.persistent_on_shell`: a persisting state
(`PMConstants.OnShell.persistent_single_frequency`) has one energy and one mass on its support, i.e. is
an on-shell mass eigenstate; `branches_do_not_persist` shows cross-branch
superpositions beat. Identifying an external particle with a persisting substrate
state remains a model input.

### Charged density and wall leakage

`PMAction.WallRestChirality.chargedPart_is_native_density` identifies the retained `(d, b)`
coordinates of the two-wall model with the native chiral density projector.
At rest, `ExactZeroMode.H` couples only opposite chiralities. Its two chiral
eigenvalue equations force equal squared norms in the two sectors for every
nonzero real eigenvalue. Thus a unit-normalized mode supplies exactly half its
squared norm to the charged density (`PMAction.WallRestChirality.charged_weight_half`).

For orthonormal daughter columns in the full wall space, `daughter_sum_eq_projection`
gives the sum of squared density amplitudes as the squared norm projected onto
their span. With an isometric generation rotation on the charged sector,
`density_strength_eq_half_fraction` gives one half of the projected fraction.
The common half cancels in a ratio of two such unweighted strengths (with
nonzero calibration strength). These identities use no measured mixing entries
or fitted wall weights. `paired_window_strength` proves that a window of
complete nonzero-energy chiral pairs gives twice the unweighted density
strength of its positive-energy subset. The factor cancels against the muon
strength if both windows meet the same conditions. For the factorized contact
model with two massless spectators, `contactWeight_open` supplies the exact
integrated weight for a massive daughter. `contact_channel_pos_iff` gives a
strictly positive contribution exactly for an open channel with nonzero
amplitude (and nonzero contact coupling). For two spectator masses
`m₁, m₂`, `PairInvariantSpectrum.massive_pair_window` proves the open
pair-invariant interval `(m₁ + m₂)² < s < (m − μ)²`. Its interior exists
exactly when `μ + m₁ + m₂ < m` (`massive_channel_open_iff`). The positive
rest momentum of the pair exists at every energy above its threshold.
`MassiveVolume.shell_density_at_energy` supplies the pair shell factor for
all nonnegative spectator masses. `MassivePair.pair_contraction` transports
and contracts the massive tensor. `PairInvariantSpectrum.massive_contact_density`
then multiplies the angularly averaged V–A rate by the recoil measure and
parent flux. Its integrated weight `massiveContactWidth` is a one-dimensional
integral over the physical daughter-energy interval and vanishes for a closed
channel. The two-massless-spectator limit agrees exactly with the earlier
integrated width. The native amplitude and physical state assignment
are still needed to apply these contact weights. At exact resonance,
`PMAction.WallGapCalibration.stationary_charged_fraction` realizes every
normalized charged fraction in the one-leg stationary family.
`PMAction.NativeWallOffset.rest_offset_breaks_chirality` shows that a retained
one-wall lazy offset breaks the chiral anticommutation even after a common
energy shift. In that case the off-diagonal model's paired-window factor
requires rechecking against the new spectrum.

**Daughter channels (closed item).** The parent is the wire's light mass
eigenstate: a persisting state is on shell
(`ExternalStates.persistent_on_shell`). The daughters are the light modes.
The gapped modes are closed channels by the spectrum's order alone. A
light parent at rest releases less energy than its own mass, which is at
most the light band's top. Every gapped mode lies above the gap, which is
above that top (the light band is defined by the gap;
`PMAction.LightLeakage.leakage_bound`). So no gapped daughter is
kinematically open in any decay of a light parent, and current weight on
gapped modes is lost. On the bare derived wire (`s = 1`, `k = α/2`) the
gap is `4–47` times the light band's top for `1/2 ≥ r ≥ 1/8`
(`tools/wall_gap_check.py`). The contact weights above apply to the light
modes alone. Comparison (not a derivation input): with weights fitted to
recorded masses, `tools/first_row_readout.py` gives leakage `≈ 0.25 r²`;
with the `1/516` dressing, the measured first-row deficit then prefers
`r ≲ 0.07–0.12`, while PMAction's explored schedules give
`1/8 ≤ r ≤ 1/2`. That is a recorded tension, to revisit once the
schedule and readout are derived. The native current on these states is
PMFlavor's.

## Protocols and the 16-channel inventory

Paper V's §4 reads the 16-channel substrate as four base routing protocols, two
routing modes, three anchors and a single sterile vacancy. `ProtocolInventory`
proves the *stipulated* inventory is internally exact and agrees with Paper III:

- `channels_card`: 16 channels (`ν = 16`).
- `two_routing_modes`: 12 route through the colour bulk, 4 do not.
- `hand_split`: 8 active (left-handed boundary), 8 static.
- `anchor_split`: 12 manifold (D=4), 2 boundary (χ=2), 2 unanchored.
- `inventory_split`: up 6, down 6, electron 2, neutrino 1, sterile 1 (= 16).
- `baseProtocol_cases`: exactly four base protocols (`electron`, `up`, `down`, `neutrino`).
- `sterile_iff_no_base`: the sterile vacancy is the unique uncoloured, static,
  unanchored channel.
- `baseProtocol_charge`: the structural classification reproduces Paper III's
  generator charges (`up=2/3`, `down=-1/3`, `electron=-1`, `neutrino=0`).
- `colourBulk_false_iff_leptonic`: the no-colour channels are exactly the
  integer-charge (leptonic) ones (`ChargeProtocols.integer_iff_colourless`).

This checks the paper's enumeration/counting; it does **not** derive the physical
identification of those channels with particles (the paper calls the inventory
stipulated).

**Decay dynamics as routing change (`ProtocolDynamics`).** The paper models decay
as a change of routing protocol. `ProtocolDynamics` makes that concrete on the
inventory: resonant tier labels `Tier = Fin 4` (`Δ⁰…Δ³`), `baseCharge` per base protocol
(up 2/3, down −1/3, electron −1, neutrino 0), and `Decay p ds` = a nonempty exit
cohort with the parent's total charge and every daughter strictly lower-tier.
Proved: `decay_charge` (charge conservation), `decay_tier_lt`, `no_infinite_chain`
(finite descent, matching "at most `L(s₀)` steps"), `tier_zero_terminal`, and the
muon example `muon_decay` (`e+ν+ν̄`, charge `−1 = −1+0+0`). Partial-width addition
and branching normalization are in `Widths` (`branching_normalized`, `total`,
`identical_channels`); competing hazards are in `Survival.competing_hazards`.
**Routing caveats (`ProtocolCaveats`).** The paper states that routing alone does
not force stability or reachability; both are proved as countermodels:
`lower_latency_not_reachable` (a strictly lower-latency, same-label state that is
not a step) and `routing_not_terminal` (a non-terminal state). Together with
`Routing.minimum_terminal` and `Routing.no_infinite_descent` these pin down exactly
what the routing axioms buy. The **specific** allowed routes and rates remain model
inputs. **Tier ladder:** the
tiers are a point (`Δ⁰`), then 1D (`Δ¹`), 2D (`Δ²`), 3D (`Δ³`) — four geometric
tiers. Each protocol's mass ledger occupies a subset (leptons/down 0,1,2; up-type
0,2,3). The draft's earlier "three generations" wording was corrected in
`4_protocols.tex` to this "point then 1,2,3 dimensions" phrasing; no tier beyond
the volume (`Δ⁴`) exists.

## Substrate existence ledger

`SubstrateLedger.substrate_has_components` answers the prior question *does the E8
substrate even have the objects Paper V identifies?* Each conjunct is an existence
witness from the actual Paper II/III constructions: a nontrivial chirality
involution and a rank-two chiral projector (`chirality_exists`,
`chiral_sector_dim_two`); three colour axes and a traceless colour generator
(`colour_axes_exist`, `colour_generator_exists`); the charge spectrum
`{2/3,−1/3,0,−1}` (`charge_values_attained`); all four base protocols plus the
sterile vacancy (`protocols_attained`); and the four-tier ladder
(`tier_ladder_exists`). The physical particle identification remains a proposed
correspondence, not an assertion of this ledger.

## Interpretation boundaries (what is *not* selected)

Proved physics here is **conditional** on a tree-level V−A contact interaction,
on-shell external states (`ExternalStates`), the flux `1/(2m)` (the definition of a
rate) and, for the corrected muon lifetime, the supplied one-loop factor. The
two-body volume `1/(8π)`, the angular density `1/(32π²)` and the electron measure
are derived from the Lebesgue measure on `ℝ³` (`PolarMeasure`, `PairSphere`,
`ElectronMeasure`). Not selected: that the contact vertex is the substrate's
physical interaction; the flux; radiative corrections; the particle/mass ledger; fermionic statistics
and asymptotic-particle interpretation; the decay-law subsystem/environment. The
`M⁵` law is a consequence of the contact model, not a universal rule for every
persistent excitation.

## Verification

Run `./build.sh PMElementaryParticles` for current counts. The sibling `PMAtoms` library is documented
separately in `PMAtoms/`; this file covers only the elementary-particle `PMElementaryParticles`
library.
No Paper VI imports; permitted axioms `propext`, `Classical.choice`, `Quot.sound`.
Run `./build.sh PMElementaryParticles` for current numbers.

## Finite decay machinery

The finite-channel rate layer used at every level (leptons here, hadrons in `PMHadrons`,
nuclei in `PMAtoms`): a rate is `β·c0` times the selected weight of a finite set of open modes,
and the mean life is its inverse.

| Module | Checked result | Retained inputs |
| --- | --- | --- |
| `LatticeSpectral` | Dirichlet eigenvalues of the finite cubic lattice used by the spectral channels | |
| `MeanLife` | `MeanLife lam = 1/lam`; `MeanLife_eq_integral` (integral of `exp(−lam T)`); `MeanLife_eq_survival_integral` (same with `ExponentialFilter.survival`); `persistenceRate = β·costRate`; `meanLife_from_persistence` | the three persistence premises of `HazardForm`; the cost rate and `β` |
| `RateModel` | `channelCost = expectedCost c0 E`; `channelRate_eq : rate = β·c0·Σ prob`; `channelMeanLife = MeanLife (channelRate …)`; zero-probability channels have zero rate | the event family per channel, and the toll/hazard coefficients |
| `BetaLattice` | `BetaLatticeChannel` (`modes`, `active`), `event`, `family`; `betaLatticeRate = β·c0·active/(modes+1)`, `betaLatticeLifetime`, positivity; `betaSpectralWeight = exp(−λ)`, `betaWeightedRate`, `betaSpectralRate`; `betaOpenModes`, `betaSpectralRateCutoff`, positivity, `betaWeightedRate_le`, `betaSpectralRateCutoff_le` (`rate ≤ β·c0`); general gap lemmas `dirichletEigenvalue_mono`, `dirichletEigenvalue_ge_next`, `betaOpenModes_eq_univ_of_twelve_le`, `betaOpenModes_eq_singleton_of_gap`, `betaSpectralRateCutoff_eq_one_of_openModes_eq_univ` | numerical spectral sum / neutron benchmark |
| `LeptonLattice` | finite lepton channel reusing `BetaLattice`; `leptonLatticeRate`, `leptonLatticeLifetime`, positivity | lepton eigenvalue input |
| `LeptonLifetime` | `muonSpectralFraction`, `muonFiniteWidth`, `muonFiniteLifetime`; minimal-cube lepton channel | mass/phase-space coefficient still continuum |

## Results of the 2026-11-16 review

- **The protocols cannot read the wire's spectrum directly** (`PMAction.WireLightBound`; numerical scans
  over each protocol's `δ_O` and cycle phase): up and leptons fail with the linear readout, all three
  with the squared one. The readout is the open item (REVIEW).
- **Doublet structure** (Lean): weak partners are antipodes and native words commute with the antipode (`DoubletSign`); on the wire the antipode is a global sign, so partners are not wire modes (see "Protocols are not wire modes").
- **Map and gate** (Lean): `RefreshMap` (clean active rows are the requirement; clock mask changes
  close over a cycle, `clockRoute_closes`); `CoherentGate` (a full position bit per event for overlapping
  weak-pair output columns); the record system has zero margin (`untouched`, `restores_iff_visits`).
- **Withdrawn** (git history has them): everything built on the 2026-11 "corrected" carrier placement:
  the per-protocol margins `64.7 / 18.6 / 11.5`, the information-theory rates `R_p`, the gains and their
  orderings, the second-ratio fits, the up heavy-entry candidate, the protocol-level `U` tests, and the
  same-wire neutrino readout exclusion; `BetaReference` (`β` carrying the up protocol's carrier onto the reference,
  axis-placed protocols) and `UpDownWire` (equal mass product for up and down on the axis-placed wire
  with `(K, k_c, k_s)` on the other wall), both modules removed. Excluded independently of placement: equal gate angles from
  the CC vertex, decay direction, `T₃` or charge squared; exclusion blocking (`2/3`); a wall-dependent
  Wilson `r_O` (`PMAction.WilsonPointForced`); reflection-invariant gains.
