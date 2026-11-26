# PMElementaryParticles — overview of checked results

Fermion masses: one reading, the occupancy cost (see [TODO](TODO.md#occupancy-cost)). The rest-gap, wire-Schur and restoring-capacity readings were retired on 2026-11-25; recover from git at `a4572b73420a60f95ca14b0376b5df3ba6c5e681`.

See [WireSchedule](WireSchedule.lean) for conditional route scheduling and [PolarMeasure](PolarMeasure.lean) for the lattice-to-continuum note.

The single map of what Paper V proves and what later work can reuse. Open work is
in [`TODO.md`](TODO.md); build instructions are in
[`README.md`](README.md). Sources are under `PMElementaryParticles/`, imported by `PMElementaryParticles.lean`.
Theorem names are entry points, not exhaustive lists; the Lean source is ground
truth. Library order: PMSubstrate → PMAction → PMConstants → PMKAutomaton → PMElementaryParticles → PMFlavor → PMHadrons → PMAtoms → PMCosmology (`AuditDependencies`). This folder imports nothing from PMFlavor.

For the remaining physical inputs, see the [EP open list](TODO.md).
The transport laws are exposed by the [conditional interface](../PMKAutomaton/COMPONENTS.md#kautomaton-closeout).

## Narrative

EP runs on KAutomaton's certified machine: the E8 lattice with the 43-tick
clock, the reversible receiver ring, the bit rings and the phase-to-record
converter. An EP program (`EPSpine.Program`) is a label, a generation (one of
the three glue cosets), a reference, firing patterns on the 43-site clock ring,
and an E8 packet in its coset. Ring steps are spacetime root events: they move
the packet's site and keep its generation and its label. The six pillars
(`ProgramWitness.Pillars`, each linked to its requirement) select the
programs: the substrate's observables leave six label classes, Map removes the
one invisible class, and every remaining class runs in every generation at the
least Toll for fifteen generation-by-class indices (`EPLabelGen.spine_generations`). What remains is
the readout (masses and widths from the programs), the vacuum and composite
placement, and multi-protocol composition. Legacy species, tier and
heavy-label ledgers are retained below with their audited status.

## EP persistence rebuild — structure

1. **Machine EP uses.** KAutomaton's interface (`PMKAutomaton.Interface`,
   `PMKAutomaton.Values`), the clock ring (`ClockRing`, `ClockSites`,
   `ClockAlignment`), the receiver ring (`RingReceiver`), the isolated
   excitation (`IsolatedExcitation`, `IsolatedReceiverTrace`), the bit rings
   (`RecordPortIdentification`) and the converter (`PhaseToRecord`,
   `CommonComparator`).
2. **Program.** `EPSpine.Program` on the 43-site clock ring; generation-blind
   ring dynamics (`EPSpine`), the label on the packet (`EPLabel`), and the
   per-generation channel placement (`EPLabelGen`).
3. **Pillars.** `ProgramWitness.Pillars` on the 43-ring, with the requirement
   links (`capacity_realizes` … `governor_realizes`); the structural ring
   results are in `RingRates` and `RingSurvivors`.
4. **Classes and witnesses.** `ProgramClasses` (six classes, one invisible) and
   `ProgramWitness` (a running program per visible class); the spine is
   `EPLabelGen.spine_generations`.
5. **3-ring checks.** The earlier toy-ring `Protocol`, its pillar predicates
   and the survivor enumeration are certificates in PMChecks
   (`PMChecks.PMElementaryParticles.Protocol`, `.PillarPredicates`,
   `.SurvivorClasses`); not in the default build.
6. **Legacy results and status.** The old species, tier, generation and
   heavy-label material is retained as a legacy ledger, audited below.

### Program classes (the EP end state)

`EPSpine.programs_card` counts 15 witness indices from three generations
and five visible classes. `ProgramClasses.visible_channels_card` counts
15 visible channel labels. Indexing every channel label in every
generation would give 45 label indices. The spine supplies one witness per class and generation. `EPSpine.witnessAt_registrations` checks its bit-ring visits.

EP's target is a classification: up to the substrate's symmetries, the
programs that meet the six pillars form a finite set of classes, each with a
witness program and a readout. The label part is in `ProgramClasses`:

| Step | Statement | Lean |
|---|---|---|
| Classes | Weak and colour actions split the 16 channels into 6 orbits. | `classOf`, `classOf_flipWeak`, `classOf_permuteColour`, `classOf_surjective`, `class_transitive` |
| Invisible class | Exactly one class is fixed by every action and has zero wall charge (the carrier charge, `CarrierChannels.hyper`): the positive lepton-axis carrier on the wall without the reference. | `unmoved_iff`, `charge_zero_iff`, `invisible_iff` |
| Map | Read with the substrate's observables, Map removes that class. Five classes remain across 15 visible channel labels. Each class has one representative per glue generation, for 15 witness indices. | `visible_class_iff`, `visibleClasses_card` |
| Generation-blind ring | A ring step is a spacetime clock-axis root (glue key `0`), so it never changes a packet's coset; `n` steps keep the coset and move the receiver site `n` places, forward or back. | `EPSpine.clockAxis_key`, `step_keeps_generation`, `forward_walk`, `backward_walk` |
| Program on the node machinery | `EPSpine.Program`: label, generation (one of 3 nonzero glue keys), reference, firing patterns on the 43-site ring, and an E8 packet root in the program's coset; the start site is the packet's clock reading. The packet stays in its coset and tracks the ring. | `Program`, `generation_card`, `program_walk` |
| Spine | Every generation and every visible class has a program meeting all six pillars; the singlet has none; `3 × 5 = 15`. | `EPSpine.spine`, `singlet_no_program`, `programs_card` |
| Label on the packet | A labelled packet is a coset root plus the label's channel vector. Its state is site (clock reading), generation (glue key) and label (internal content: pairings with the internal simple roots). Channel vectors carry no glue key; ring steps have zero internal content; distinct labels have distinct internal content. So a ring walk moves only the site: generation and label are conserved and the label reads back at any time. | `EPLabel.channel_glueKey`, `clockAxis_internalContent`, `channel_internalContent_injective`, `walk_keeps_label`, `label_readout`, `labels_distinct`, `spine_labelled` |
| Placement per generation | Generation `g`'s channel vectors are the certified internal triality applied `g` times to the reference placement. In every generation every channel sits in the class the library wall rule requires (`wallClass g (active c)`), carries no glue key, and the labels stay distinct. The spine holds per generation with each generation's own channel vectors. | `EPLabelGen.channelE8Gen`, `channelKeyGen_wallClass`, `channelGen_glueKey`, `channelGen_internalContent_injective`, `genIndex_bijective`, `spine_generations` |
| Per-wall symmetry | The 16 channels are two walls of 8 carriers. Within one wall, colour exchange and the weak flip keep every lattice pairing of the placed vectors, in all three generations, and both moves keep a channel's wall. The transpositions generate the colour group, so this is group invariance. Pairings between the two walls are not substrate costs and no symmetry is claimed for them. | `EPLabelGen.colour_wall_invariant`, `weak_wall_invariant`, `colour_preserves_wall_pairs`, `weak_preserves_wall_pairs` |
| Witnesses | Every visible class has a 43-ring program meeting all six pillars: least-Toll reference (Hamming `1` for every label), one firing site per ring, exactly one registration per ring per period, at the least Toll. The invisible class has none. | `ProgramWitness.visible_class_has_program`, `leastRef_hamming`, `witness_pillars`, `witness_total`, `invisible_class_no_program` |

The record-bit Map of the 3-ring `PillarPredicates` (PMChecks) does not see
charge or chirality and keeps six. Open: the generation readout, and the neutrino mass without
the singlet.

### Current status and legacy ledger

- Machine and program: `EPSpine.Program`, `ProgramWitness.Pillars`.
- Survivors on the 43-ring (`RingSurvivors`), proved without enumerating
  firing patterns:

  | Pillar | Statement on the 43-ring | Lean |
  |---|---|---|
  | Toll floor | A bit ring registers in one period iff some site carries a request. Toll excludes exactly the empty pattern on a differing ring. | `first_arrival_floor`, `sum_zero_iff`, `ring43_toll_iff` |
  | Least Toll | Every Toll-admissible pattern costs at least the Hamming distance to the reference. One firing site per differing ring attains it. | `ringTotal_ge_hamming`, `ringTotal_oneSite` |
  | Minimum | One firing site gives exactly one registration per period. | `one_site_floor`, `RingRates.ring43_one` |
  | Margin | Two adjacent firing sites trap the packet: 43 registrations in 43 ticks. Margin excludes this case. | `trapping_saturates` |
  | Map | The reference-equal label is excluded (record level); the invisible class is excluded (class level). | `ProgramWitness.MapRecord`, `ProgramWitness.MapClass` |

  Least-Toll references per label: up→lepton, down→colour, electron→lepton,
  neutrino→colour (Hamming `1`, `bitToll_eq_hamming`). The 3-ring counts
  (`robustCoreU_card = 1110`, `SurvivorsU false = 1650`) are toy-ring
  observations, not E8 values.  These counts are the `SurvivorClasses`
  certificate in `PMChecks`; not in the default build.
- E8 attachment: `ChannelVectors.channelCoord`; active-false vector class,
  active-true certified triality image (`channelCoord_glueClass`,
  `channelCoord_injective`, `channelCoord_image_card`).
- References: lepton `+2e_0`; colour `{+2e_1,+2e_2,+2e_3}`, from
  `RecordCoordinates.labelRecord_eq_axis_sign` and
  `ChannelVectors.vectorCoord_eq_carrier`.
- Missing: shared/composite background, multi-protocol composition and the step-to-cost rule.
- Legacy status: `ProtocolInventory`, `QuarkMasses`, `LeptonMasses`,
  `TierLedger` and `HeavyFlipRecords` carry the audited statuses in their
  module docs; tier sets, generation addresses, quark/lepton formulas and the
  heavy-label weight remain premises.

**One firing site on the receiver ring.** The live packet walks forward to
the firing site `s` (`RingRates.quiet_walk`), is exchanged onto the record
stream and registers (`portStep_fire`), then walks backward (`record_walk`)
and reaches `s` again only after a full lap (`symm_iterate_ne_self`). So one
firing site registers exactly once in every `n`-tick period, for every ring
size `n`, start site and guard (`RingRates.one_site_exact`, structural, no
kernel enumeration). On the clock ring `n = 43` this is `ring43_one` and
`ring_Delta_one` (linked to `ClockSites.ring_size`).

The registration counts `14, 15, 21, 22, 28, ...` are **3-ring toy values**,
not E8 values. For any firing pattern, the packet walks the ring until its
first exchanging site and registers there within one period
(`RingSurvivors.first_arrival_floor`, any `n`).

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
lifetimes in seconds, with their bounds, and the program spine (`Generation`, `generation_card`,
`visibleClasses_card`, `visible_channels_card`, `invisible_iff`, `Program`, `programs_card`,
`spine_generations`). Prove a bound in its own module and name it in `Values`. `Values` holds no
computation. `e8p` reads EP only through `Values`.

Shared units and couplings used by every level are in `SharedUnits` (`me`, `ħc`, `α`, `α⁻¹`,
their bounds, and `G_F` in `m_e⁻²`).

## KAutomaton dependence of EP results

**[Premise]** marks an identification, circuit choice or population
that is supplied. Each certificate applies on its explicit inputs.

| EP result | KAutomaton inputs | Where the input enters |
| --- | --- | --- |
| Admitted serial route and periods | G, T, L, O, Q, J | `WireSchedule.Premises` and the admitted placements supply clock calibration, route, occupancy, renewal and shared jobs. [Premise] The schedule is a serial template. |
| Heavy guard, bank and readout | G, U, W, O, Q, T | `HeavyFlipControl`, `ElectricCompanionBank` and `ElectricChiralKick` give conditional maps on a supplied seed, record, support and phase. [Premise] The physical heavy branch reads that record. |
| Booked writer mass and reference | O, H, G, W, D, K, B, J | `WireReferenceCost` takes a booked population or an explicitly declared sampling policy, plus the paid remainder and erasures. [Premise] Uniform sampling and either reset account need their own booking. |
| Heavy attenuation and down identity | G, U, W, D, K, B | `WireSchedule.bitToll` takes the reference. `WireSchedule.amplitude` takes the unpriced terms and booked schedule. `HeavyFlipRecords.down_geometric_mean` takes the common bit price in the colour polarity. |
| Lightest charged response and order | G, U, T, W, D, K, L | `ChargedInsertion.det_flip_at_resonance` takes the offset, calibrated detuning and cycle weights. [Premise] Matched ports are physically admitted. Neither the matched flags nor the route fixes the offset's scale. |
| Tier and species masses | G, U, O, T, L, K | `TierLedger.wireTier` takes the address-to-tier assignment. [Premise] The legacy lists and the named formulas in `QuarkMasses` and `LeptonMasses` are ledger identifications. Their E8 arithmetic is checked. |
| Decay and subsequent current readout | U, W, G, T, O | The decay theorems on supplied on-shell states, current and support are conditional. [Premise] A physical association of the wave and species requires its admitted trace. |

### Public KAutomaton imports

EP imports only `PMKAutomaton.Interface` and `PMKAutomaton.Values`
from KAutomaton. Nine Machine import statements across seven
files were consolidated. The added aliases under `Interface.Wire` are:

| Section | Exports |
| --- | --- |
| `Carrier` | `lookup`, `lookup_antipode`, `carrierTriality`, `carrierTriality_vector`, `carrier_is_glued`, `diagonalRoot`, `glued_triality_step`, `trialityMatrix`, `triality_cube`, `triality_observed`, `triality_unitary` |
| `Glued` | `M`, `Wt`, `bit`, `carrier`, `crossing`, `dot`, `neg_class`, `neg_ne`, `refl`, `reflectPair`, `root`, `runCrossing`, `triality`, `wallStep_class` |
| `RootBranch` | `embed`, `population`, `root_action`, `swap` |
| `Registers` | `current`, `current_observed`, `current_unitary`, `evolution_occupation` |
| `Probe` | `events`, `record`, `schedule_closes`, `scheduled_read`, `State`, `fire`, `update` |

**Certified coin and coherent ring step.** The converter's pass and flip
amplitudes are `(1 + e^{ix})/2` and `(1 - e^{ix})/2` (`converter_plus`,
`converter_minus`), i.e. `cos(x/2)` and `sin(x/2)` up to the common phase
`e^{ix/2}`. `encounter_unitary` gives the coherent one-site encounter. At
`x = π`, `exact_bit_flip` gives pass amplitude 0 and flip amplitude 1.
`CoherentRing.ringShift` is the direction-dependent site shift and
`CoherentRing.ringTick_unitary` proves the full-firing tick
`(1 ⊗ encounter x) * shift` is unitary for every `n`.

**Phase-to-record converter.** The certified comparator
`CoherentComparisonRepair.compare (InterferenceReadout.phase x)` is unitary
(`PhaseToRecord.converter_unitary`). On the phase-encoded input `phaseInput`,
the minus output has probability exactly `DiagonalReadout.flag x`
(`minus_probability`), and the expected receiver flag is `flag x`
(`expected_receiver_flag`). The converted branch records are orthogonal
(`converted_records_orthogonal`, `converted_branch_records_unequal`), and
`bitToll_eq_expected_conversion` recovers the EP row. The factor of two is the
phase encoding (`nsq/4`) versus orthogonal receiver encoding (`nsq/2`). Gap U's
flag identification closes for all phases; no new unitary was defined.

**Common comparator.** Receiver and electric flags share the
`CommonResponse` parent only up to normalization. `CommonResponse.stateFlag` is
`nsq(φ − Uφ)/4`; `DiagonalReadout.flag` is `(1 − cos x)/2`, and
`DiagonalReadout.state_flag` is the weighted diagonal average.
`CommonComparator.exchangeFlag_eq_two_linkFlag` makes `exchangeFlag` twice the
identity `linkFlag`; `CommonComparator.flag_eq_stateFlag` makes the electric
flag the unit-phase `stateFlag`. EP's exact record bits are
`DiagonalReadout.flag` values (`ElectricHeavyRecord`, `bitToll_eq_hamming`).
The factor-two normalization remains, so this is not a certified identification;
gap U stays open. KAutomaton W and G are now certified and removed from its open
ranking.

**EP protocol layer.** `IsolatedReceiverTrace` and
`RecordPortIdentification` are EP protocol work running on the KAutomaton
machine; they are not KAutomaton results. EP now owns the retained request field
and firing pattern G, the excitation occupancy and reference-record choice O,
the label record/reference/theta part of U, which label record W reads, the
label Toll/paid-event part of K, and the history/prior family H. KAutomaton keeps
the common comparator, receiver-flag computation, tariff unit, links, boundary,
clock and job mechanics. The label dependence is certified by
`bitToll_eq_hamming`, `refRecord`, `bitRingTotal43_eq` and `firingPattern`.

### Isolated-excitation input and trace

The isolated input is the stationary E8 background plus one 16-slot packet
label (`IsolatedExcitation.occupiedInput_valid`, `occupiedInput_admitted`).
The retained receiver state and occupancy checks are
`IsolatedReceiverTrace.localizedPorts_occupancy` and
`localized_occupancy_preserved`; requests are retained
(`localized_requests_retained`) and the 3-ring sum is
`localizedSum43_eq_pattern`. These are **3-ring toy values**, not E8 values;
the 43-ring one-site count is in `RingRates` above.

### Finite witness output

`TransportCandidates` (its own module; `e8p` does not read it) keeps only the uniform control field. Its
receiver column is zero by equal arrivals; it is not a one-excitation result.
The localized 43-tick sums are `patternSum` of the firing pattern,
conditional on the exchange pattern from the retained request field
(`localizedSum43_eq_pattern`). These are **3-ring toy values**, not E8 values.
The record Toll is
a separate column. The heavy
reference, the static offset, and the wire-to-tier map remain explicit inputs.
See
[the e8p report](../../tools/e8p/README.md#ep-uniform-control).

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

## Charged insertion on the static wall

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

The [charged lift below](#the-charged-lift) counts the
same selector and crossing support for every charged label.
`det_flip_at_resonance` gives the same linear response to the supplied
offset in each selected sector. Its order in `1/Δ` depends on the firing
law for that offset.

The [phase and handoff calculation](#phase-handoff-and-toll)
separates the selector's phase distance from a spatial layer count.
The uncompensated comparison gives flags `½, 1, ½` for electron, up and
down. The selected label gives zero flags in both matched comparisons
(`matched_flags_zero`). A through admittance is a transmission
probability. A registration Toll supplies a survival amplitude.
The pulse needs a native schedule before either law can assign its size.

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

### Heavy flip and record certificates

`WireReferenceCost.reference_threshold_with_erasure` shifts the
output-flag threshold by the difference in booked writer erasures.
The balanced comparison reset keeps its own conditional thresholds.

<a id="finite-control-of-the-direct-heavy-flip"></a>
<a id="record-comparisons-and-heavy-flip-toll"></a>
<a id="an-electric-charge-record-on-both-walls"></a>
<a id="four-port-electric-record-with-fixed-kicks"></a>
<a id="electric-decoder-on-the-odd-coordinate-bank"></a>
<a id="short-root-decoder-and-serial-frame-bound"></a>
<a id="primitive-flags-of-the-short-electric-decoder"></a>
<a id="electric-kicks-from-the-chiral-register-current"></a>
<a id="triality-preparation-on-the-companion"></a>
<a id="primitive-crossing-activity-and-clock-limits"></a>
<a id="other-heavy-weight-diagnostics"></a>

| Theorem or module | What it proves | Conditions |
| --- | --- | --- |
| `HeavyFlipControl.direct_iff`, `ReferenceClassHop.touches_reference_class`, `no_root_only_direct_address`, `flip_encoded`, `flip_light` | The direct address is zero. Untagged roots alias other addresses. The addressed crossing fixes light inputs. | Chosen reference class and supplied generation address. The reverse uses the inverse word. |
| `record_colour`, `record_opposite`, `write_clean`, `registered_word`, `registered_phase_unitary` (`IndependentRegisters`, `RegisterControl`) | Two bits are preserved across walls and colours. The clean write and guarded exchange are reversible. The phase has coefficient `(1−z)/2` on exchanged endpoints. | Occupied banks, clean record and supplied joint control. |
| `CompanionHeavyFlip.ready_pack`, `run_pack`, `run_twice_pack`; `CoherentGate.tensor_dot`, `unequal_needs_orthogonal` | Ordered companion classes recover the heavy address. The update transfers the companion class and returns after two runs. Overlapping weak outputs need orthogonal records. | Packed companion and retained record. |
| `HeavyFlipRecords.quark_auxiliary_gap`, `no_exact_quark_record`, `electron_down_overlap` | Auxiliary outcome gaps for up and down are at most ½. Electron/down squared overlaps at `3π/2` and `π/2` are 1 and ¼. | Shared auxiliary-only hypercharge control with the massive slots left in place. |
| `full_only_minimum`, `quarter_massive`, `paired_minimum`, `paired_tolls`, `paired_ladder`, `paired_gap_ratio` | Full and lepton-only flag ledgers in order e,d,u,ν are `(¾,¾,¼,¼)` and `(¾,(3−√3)/8,(5−√3)/8,¼)`. Their sum gives the charged ladder and gap ratio `2/(3+√3)`. | The relevant visits are independently required and each state flag is charged. These comparisons do not supply the exact record. |
| `orbit_bit_price`, `orbit_record_minimum`, `orbit_record_tolls`, `orbit_record_ladder`, `down_geometric_mean`, `PMAction.TollAmplitude` | The two exact bit visits cost `(2,1,0,1)` in the stated polarity. Down's amplitude is the geometric mean for any common price per bit registration. | Admitted signed-axis phases, clean branch and a separate requirement for each bit. |
| `ElectricHeavyRecord.electric_generator`, `charge_from_bits`, `position_time_minimal`, `sector_time_minimal`, `same_wall_pair`, `packet_kick_phases`, `root_writer` | The electric charge gives the same record on either wall. The principal phase parameters are `3π` and `3π/2`. A quarter preparation, signed kick and three-quarter inverse write the basis record. | Matching-position reference, moving root orbit and supplied joint coupling. |
| `colour_reference_toll`, `lepton_reference_toll`, `reference_flags_from_orbit_bits`, `embedded_step_flag`, `pulse_flags`, `two_bit_factor_toll` | The electric references share the position flag and complement the sector flag. Their two-bit totals are `(2,1,0,1)` and `(1,2,1,0)`. The exhibited writer's three factor flags give `1 + T_bits/2` for two writes. | Choose either comparison-output flags or the exhibited factor flags as paid registrations. These are distinct ledgers. |
| `ElectricFourPortRecord.phase_codes`, `read_exact`, `decoder_word`, `exposure_eq_flags`, `exposure_tolls`, `forward_tolls`, `forward_no_ladder` | Fixed kicks and a decoder write four orthogonal records. Exposures tie electron and down. The forward logical-factor ledgers put down below electron in amplitude. | Prepared balanced bank and one registration per indicated flag. |
| `ElectricDecoderBoundary.phase_word_not_quarter`, `phase_word_not_decoder`; `ElectricCoordinateDecoder.decoder_unitary`, `decoder_observed`, `decoder_reads`, `prepare_balanced`, `encoded_flag` | Uniform-line permutation phases cannot supply the literal decoder. Odd coordinates realize it and expose the primitive state flags. | Coherent root-phase contract, common rate and supplied seed. |
| `short_observed`, `short_reads`, `record_at_short_port`, `short_unitary`, `short_word_exact`, `short_duration`, `undo_word_exact`, `short_prepares`, `undo_duration`, `fresh_bank_serial_exceeds_clock` | The short decoder writes bit-reversed records. Decode and fresh preparation take 25 and 27 quarter-times. | In serial, a fresh bank exceeds one frame when a quarter-time takes at least one tick. |
| `ElectricPrimitiveToll.primitive_decoder_flags`, `ledger_observed`, `forward_tolls`, `charged_ladder`, `canonical_tie`, `preparation_flags` | Short decoder plus exposures give `(3,5/2,2,1)`. The canonicalizing swap ties down and up. Inverse preparation adds one flag. | One registration per executed state flag and an occupied clean seed. |
| `ElectricChiralKick.high_observed`, `low_observed`, `kick_on_summand`, `high_unitary`, `high_preserves_occupation`, `two_kicks_from_one_current`, `swapped_exposure_toll`, `total_tolls`, `total_ladder`, `total_toll_wall_pair`, `clean_first_seed_at_rest`, `balanced_bank_leaves_rest` | `PMAction.RegisterInteraction.current` and the swap give the two kicks. Forward Tolls are `(13/4,11/4,5/2,1)`. A balanced bank needs a gapped coordinate and separate carrier. | Supplied current and one registration per executed state flag. |
| `ElectricCompanionBank.triality_observed`, `prepares_companion_bank`, `glued_triality_step`, `guarded_companion_transport`, `companion_transport_observed`, `companion_transport_roots`, `written_port_ready_iff`, `setup_class_flag` | Triality prepares the bank from the predecessor seed. The guard transports it. Only the active neutral written port returns ready. The setup endpoint flags ½. | Occupied odd coordinate-zero seed in the proper class. |
| `ElectricCompanionSetupToll.short_setup_on_seed_support`, `primitive_setup_flags`, `common_setup_on_seed_support`, `equal_slot_setup_sum` | One root suffices on the active seed and two on the static seed. The mean setup flag budget is 5/8. | The certified seed support and equal wall populations. |
| `HeavyCrossingCost.activity_histogram`, `uniform_cost`, `sign_tie` | Six reflects per carrier give 27 idle, 20 unit and one double displacement across eight amplitudes. The mean charge is `(20 c₁ + c₂)/8`. | Uniform amplitudes for the mean, antipodal weights for the sign tie and supplied prices per displacement. |
| `HeavyFlipNativeBoundary.no_closed_cleaning`, `tick_event_iff`, `idle_and_excursion_counts`, `cycle_closes`; `GappedGluedCrossing.equalClass_iff` | The untagged probe aliases addresses and closed universal cleaning is impossible. Both idle and two-toggle masks close. The gapped crossing shifts generation. | The clocked endpoint needs an address and a ready record. |

[Persistence selection](WireSchedule.lean) enumerates a bounded serial family.
[Packet reference cost](WireSchedule.lean)
derives uniform weights under the full-packet sampling premise and
checks the vacancy contribution. The full-packet bit gap is `−1/2`
per sampled input when the vacancy is probed. The smaller support
and the idle-vacancy rule have separate thresholds. The
[lifecycle comparison](WireSchedule.lean)
adds a conditional half flag for a written-bit reset with a fresh
zero. Actual writer traffic and the difference in remaining paid
work still decide the polarity.

Open premises.

- Supply and renew the occupied seed, admit the joint current, controlled phases and crossing, and schedule the two wall insertions. Retain reset or export in the record trace. See the [clock ledger](../PMKAutomaton/CLOCK.md).
- Derive the event and tariff. Choose which visits register, which polarity persists, and how the displacement and preparation prices enter. For a price on the node rather than the direct flip, use `node_toll_raises_heavy`.
- The half-period and node-phase diagnostics suggest competing scores. Their selected cadence and paid visits remain open.

Comparison only. The [down mean diagnostic](../../tools/down_mean_check.py) gives `s_d/√(s_e s_u) ≈ 0.96` and inferred prices `2.04` and `2.13` in the ledger convention. The [heavy Toll diagnostic](../../tools/heavy_toll_targets.py) compares the charged gap ratios, including 1 for the short decoder and ½ for the chiral-current candidate. The [bare detuning scan](../../tools/detuning_bound_check.py) tests the `√(3/2) k` bound. These comparisons supply no scheduling inputs.

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
| `MuonLifetimeCorrected` | `τ_μ = τ_tree/(f(r)·q)`: `r = (m_e/m_μ)²` (`r_bounds`), derived phase factor `f(r) = MassiveWidth.phase r` (`phase_bounds`, `0.99981295`), `α = 1/geometricIndex`, `corrected_bounds` `2.196987–2.196998 µs`; e8p `muon_lifetime_s` | one-loop QED factor `q = 1 − (α/2π)(π² − 25/4)` (Kinoshita–Sirlin), supplied; higher orders (≈5 ppm) not included |
| `MuonQEDLoops` | The QED loop terms of muon decay at E8 inputs, in one place: the coupling at the muon scale `α_r⁻¹ = α⁻¹ − (2/3π) ln(m_μ/m_e) ≈ 135.90` (`log_muon_bounds`, `alphaR_div_pi_bounds`); one loop with its electron-mass terms (`dq1_bounds`); two loops `6.700 (α_r/π)²` (`dq2_bounds`); phase space `dq0` (derived) | the loop coefficients and running-coupling prescription (van Ritbergen–Stuart) |
| `MuonLifetimeHigherOrder` | `τ_μ = τ_tree/(1 + Δq⁽⁰⁾ + Δq⁽¹⁾ + Δq⁽²⁾)`: `lifetime_bounds` `2.196974–2.196984 µs` | via `MuonQEDLoops` |
| `TauLifetimeCorrected` | Tau lifetime from the measured `τ_μ` and supplied `B_e` with the electronic partial-width ratio corrected: phase space `f(x_μ)/f(x_τ)` (derived), `W` propagator (E8 `M_W`), one-loop QED at each lepton scale (`α(m_τ)⁻¹ = 133.3` supplied); `tau_lifetime_corrected` `291.03–291.06` fs (tree `291.15–291.17`) | measured `τ_μ`, `B_e`, `α(m_τ)` |
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
Radiative stage 2—assembling the vertex, self-energies and real emission and
showing the ultraviolet and infrared logs cancel—has not been started.
The regulated virtual
and hard-emission terms are derived numerically
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
| `TauBranching` | `B(τ→eνν̄) = 1/(1 + f(r) + N_c h)`: leptonic ratio from the derived phase factor at the E8 masses (`phase_bounds`, `0.9724–0.9727`), `N_c = D − 1 = 3` (`colours_eq`); parton level `h = 1` gives `0.2010–0.2012` (`parton_level`); the supplied `0.1782` needs `h = 1.2129–1.2132` (`supplied_needs`). The [tau inventory](../PMHadrons/OVERVIEW.md#channel-inventory-and-interfaces) uses the derived ratio | inclusive hadronic factor `h` ([PMHadrons REVIEW](../PMHadrons/TODO.md)) |
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
| `CarrierChannels` | Each channel is a wall (the reference wall is "left", `PMAction.ChiralityConvention`), a carrier axis (lepton axis `0`, colour `1–3`) and a sign; wall charge `bl` or `bl + 2 t3` and electric charge `bl/2 + t3` from the carriers (`CarrierRepresentation`); `packet_charge_eq`: the packet's charge table is this carrier charge |
| `ChargeProtocols` | Electric charge from the carriers; `thirds`; `integer_iff_colourless` |
| `LeptonMasses` | `m_μ`, `m_τ` written in canonical E8 invariants and decomposed into named tier costs (`muon_ledger`, `tau_ledger`; the `π⁺` ledger is in `PMHadrons.MesonMasses`); muon feedback derived as a recursive fixed point (`muonFeedback_fixpoint`); E8-only enclosures (measured tensions in `tools/e8p/E8PConstants/PMElementaryParticles/LeptonMassPulls.lean`) |
| `QuarkMasses` | Six quark formulas written in canonical E8 invariants and decomposed into named tier costs (`up_ledger`…`top_ledger`); E8-only enclosures (measured pulls in `tools/e8p/E8PConstants/PMElementaryParticles/QuarkMassPulls.lean`) |
| `KoideSplit` | Three amplitudes `v` (masses `m = v²`) split into a generation-symmetric part and a symmetry-breaking part, orthogonal (`normSq_split`). The Koide ratio `Q = Σv²/(Σv)²` equals `1/3 + |breaking|²/(3|symmetric|²)` (`koideQ_eq`), so `Q = 2/3` iff the two parts have equal norm (`koide_iff_equal_split`); `Q` does not depend on which coset is first (`koideQ_cyclic`). Equivalently, the two-outcome record "generation-symmetric or not" is a fair coin (`koide_iff_fair`). This is not the clock ledger's fair flag: that flag is a fidelity under the cyclic shift and equals `3/8` at `Q = 2/3` (`shiftFlag_at_koide`). In the pair-plus-one limit (two degenerate generations, one distinct; the library's equal-link-weight restoring pair plus the direct address), `Q = 2/3` fixes the distinct amplitude at `(4 + 3√2)` times the pair's (`pairPlusOne_koide`), mass ratio `34 + 24√2 ≈ 67.94`. For the Hermitian circulant `a·1 + b·P + b̄·P⁻¹` on the three cosets (stay `a`; move forward `b` on the live stream, back `b̄` on the record stream), `Q = 2/3` iff the move weight `2|b|²` equals the stay weight `a²` (`circulant_koide`); the phase of `b` is left free. Linear algebra only. Prior art: Koide (1981) for `Q = 2/3`, Brannen (2006) for the circulant form; the contribution sought is their derivation on the E8 machine. Comparison (not in Lean): the measured leptons give `Q = 0.666664`; the declared ledger gives `0.666654`; imposing `Q = 2/3` on the ledger's `e`, `μ` gives `m_τ = 3477.44 m_e` (measured `3477.36 ± 0.18`; ledger `3477.00`). |
| `KoideSelection` | Koide from the Selection Principle with one named premise: if the generation record has two outcomes (symmetric, breaking) with the norm share as its law, the persisting law (`LawSelection`: uniform, under average or worst-case rate) gives `Q = 2/3` (`koide_of_selected_average`, `koide_of_selected_worst`). Note: the Brannen cosine form is only the three-point Fourier transform and carries no content; the content is this one constraint plus one ratio (`m_μ/m_e`). |
| `KoideCosets` | Equal-weight lazy walk on one coset's clock-local roots (stay = silent, move = `±1`): `Q = 2/3` iff stay count = twice the forward count (`KoideSplit.lazyWalk_koide_iff`). Conjugate spinor `8 : 4 : 4` is Koide-fair (`cospinor_walk_koide`); vector `2 : 7 : 7` is not (`vector_walk_not_koide`); spinor never stays (`spinor_no_stay`); forward = back in all three (`fwd_eq_back`). Open: that the generation register's stay/move amplitudes are this walk's. |
| `NeutrinoContext` | Contextual neutrino masses excluded by oscillation data (`weak_minus_rest_excluded`, `no_moderate_gap_ratio`) |
| `TauLifetime` | `τ_τ = τ_μ (m_μ/m_τ)⁵ B_e` (`rate_ratio`, `tau_lifetime_tree`); measured pull in `tools/e8p/E8PConstants/PMElementaryParticles/TauLifetimePulls.lean` |

## Declared tier and species ledgers

`TierLedger` lists declared tiers. `LeptonMasses` and `QuarkMasses` evaluate declared formulas used by existing comparisons and decay calculations. The occupancy readout still needs a complete recurring program and a capacity value for each occupied resource.

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
are still needed to apply these contact weights.
`PMAction.NativeWallOffset.rest_offset_breaks_chirality` shows that a retained
one-wall lazy offset breaks the chiral anticommutation even after a common
energy shift. In that case the off-diagonal model's paired-window factor
requires rechecking against the new spectrum.

**Daughter channels.** The contact-width results apply with supplied physical states and their masses. `ExternalStates.persistent_on_shell` gives the on-shell relation. The admitted current, state assignment and open channels are needed for a decay calculation.

## Protocols and the 16-channel inventory

Paper V's §4 reads the 16-channel substrate as four base routing protocols, two
routing modes, three anchors and a single sterile vacancy. The protocol names are labels for
carriers (`CarrierChannels`): up/down are the colour-axis carriers by sign, electron/neutrino the
lepton-axis carriers by sign, and the sterile vacancy is the positive lepton-axis carrier on the
wall without the reference (`baseProtocol_carrier`). "Active" is the reference wall
(`active_eq_wall`). `ProtocolInventory` proves the inventory is internally exact:

- `channels_card`: 16 channels (`ν = 16`).
- `two_routing_modes`: 12 route through the colour bulk, 4 do not.
- `hand_split`: 8 on the reference wall (active), 8 on the other wall.
- `anchor_split`: 12 manifold (D=4), 2 boundary (χ=2), 2 unanchored.
- `inventory_split`: up 6, down 6, electron 2, neutrino 1, sterile 1 (= 16).
- `baseProtocol_cases`: exactly four base protocols (`electron`, `up`, `down`, `neutrino`).
- `sterile_iff_no_base`: the sterile vacancy is the unique uncoloured, static,
  unanchored channel.
- `baseProtocol_charge`: the labels carry the carrier charges (`up=2/3`, `down=-1/3`,
  `electron=-1`, `neutrino=0`).
- `colourBulk_false_iff_leptonic`: the no-colour channels are exactly the
  integer-charge (leptonic) ones (`ChargeProtocols.integer_iff_colourless`).

The carrier reading leaves three named premises (`CarrierRepresentation`): one axis is the
lepton axis (the reserved cell), the sign is the doublet index, and the right-wall charge adds
`2 t3`.

**Decay dynamics as routing change (`ProtocolDynamics`).** The paper models decay
as a change of routing protocol. `ProtocolDynamics` makes that concrete on the
inventory: resonant tier labels `Tier = Fin 4` (`Δ⁰…Δ³`), `baseCharge` per base protocol
(up 2/3, down −1/3, electron −1, neutrino 0), and `Decay p ds` = a nonempty exit
cohort with the parent's total charge and every daughter strictly lower-tier.
Proved: `decay_charge` (charge conservation), `decay_tier_lt`, `no_infinite_chain`
(finite descent, matching "at most `L(s₀)` steps"), `tier_zero_terminal`, and the
muon example `muon_decay` (`e+ν+ν̄`, charge `−1 = −1+0+0`). Partial-width addition
and branching normalization are in `Widths` (`branching_normalized`, `total`,
`identical_channels`); competing hazards are in `PersistenceMechanics.Rates.competing_hazards`.
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

## Line, composition and the clock

**The clock closes the receiver ring.** The clock states are the discriminant
group of the E8 clock plane `ℤcu + ℤcv` (`PMSubstrate.ClockPlane.clock_glue`,
`w ↦ w₁ − 2w₂ mod 43`). A lattice point reads the clock by
`clockReading z = (⟨z,cu⟩ − 2⟨z,cv⟩) mod 43`. `ClockRing` proves `clockReading`
additive, `rootList_complete` (from `ThetaE8.e8_card_roots`), the counts
`one_tick_roots = 22`, `minus_tick_roots = 22`, `silent_roots = 22`,
`moving_roots = 218`, and `plus_split`: eleven `+1` roots project as `(1,0)` and
eleven as `(−1,−1)`. The 22 silent roots are 20 orthogonal to the clock plane
plus `±cu`. `walk_returns_iff` says a walk of `+1` roots closes exactly when 43
divides its length, and `plus_step_rotates` identifies a `+1` step with
`finRotate 43`.

The exploration scripts for these facts are `tools/clock_ring_check.py`,
`tools/clock_tick_weights.py`, `tools/clock_slice_alignment.py`,
`tools/clock_stabilizer_orbits.py`, `tools/generation_clock_signature.py`,
`tools/clock_plane_projection.py` and `tools/bit_ring_rate_check.py` (no data).

The ring therefore has `n = Δ = 43` sites, not 3. The live stream steps by
`+1` roots and the record stream by `−1` roots; an exchange swaps a packet
between them and reverses its direction. Consequences: one firing site per
period gives exactly one registration (`RingRates.ring43_one`); any nonempty pattern registers at least once (`RingSurvivors.first_arrival_floor`), so the Toll floor is met by one firing site per period, while Margin
still excludes trapping between adjacent firing sites; a ring site is a clock
phase, matching `ClockedRootTrials` at phases 0 and 1.

**Aligned D4 and tick weights.** `ClockAlignment` certifies one placement with
simple roots `a`, `b`, `c`, `beta` (`a_mem` … `beta_mem`), inner products
`pair_a_b`, `pair_b_c`, `pair_b_beta = −1`, and pairwise orthogonality of
`a`, `c`, `beta` (`pair_a_c`, `pair_a_beta`, `pair_c_beta`). The internal D4 is
`internalRoots_length = 24`; the spacetime D4 is `spacetimeRoots_length = 24`.
The slice roots are `sliceRoots_length = 12` and clock-silent
(`sliceRoots_silent`); the clock-axis roots satisfy `clockAxisRoots_counts`:
six read `+1` and six read `−1`. The forward and backward tick sets have
`forwardRoots_length = backwardRoots_length = 6`.

The glue key is
`glueKey r = ((⟨r,a⟩+⟨r,c⟩) mod 2, (⟨r,a⟩+⟨r,beta⟩) mod 2)`. It is additive
(`glueKey_add`), vanishes on both D4s, and its three nonzero values are the
cosets. `vectorRoots_length`, `spinorRoots_length` and
`conjugateSpinorRoots_length` give 64 roots each; `vectorRoots_counts` is
`(7,7,2)`, `spinorRoots_counts` is `(4,4,0)` and
`conjugateSpinorRoots_counts` is `(4,4,8)` for forward, backward and silent
roots. `cu_key` and `neg_cu_key` place `±cu` in the vector coset, and
`plus_total`, `minus_total`, `silent_total` add the classes to the clock totals.

`ClockTickWeights` proves every slice reflection fixes the clock reading
(`clockReading_reflect`), preserves the forward and backward sets
(`forward_closed`, `backward_closed`), and acts transitively on each set
(`forward_one_orbit`, `backward_one_orbit`; two reflections suffice). Thus the
six forward and six backward steps are single orbits under the substrate
symmetries that fix the clock. Closure then gives equal weights within each set;
Closure itself is the named premise in [SCOPE](../../SCOPE.md#named-premises).

`ClockSites` identifies the receiver site with the reading:
`site z = toFin (clockReading z)`, `ring_size : 43 = Δ`,
`site_add_forward`/`site_add_backward`, and `arrivals_are_lattice_steps`: the
live arrival comes from one forward step back and the record arrival from one
backward step back. The update model and Closure are the two named premises,
not Lean theorems.

The alignment search is numerical. Over every D4 with slice D3 in the clock
plane's stabilizer A4, the clock-axis readings are `±1` in 960 labelled
placements and `±2,±4,±8` in 480 each. In the `±1` class every slice root is
orthogonal to the clock plane; every clock-axis root is a one-tick root;
`e₀ ± e₃` reads `±1`; `2e₃` reads `+2`, matching the two root events of
`AxisHop`; the six forward roots lie in one projection class and its 10-orbit,
never in the fixed roots; the two classes split 480/480; and the orthogonal
complement is again a D4. The pointwise stabilizer of the clock plane is
generated by the 20 orthogonal roots, an A4 system with `W(A4) ≅ S5` of order
120; the orthogonal roots form a second A4 containing `cu`. The 22 one-tick
roots form four orbits: one fixed root plus a 10-orbit for each projection
class. The fixed roots lie in the clock's A4; `r ↦ r − cu` pairs the classes.
These orbit and placement counts are script-level; the six-step orbit and its
equal weights are Lean-proved for the certified placement.

**Composition rules.** Capacity Partitioning is
`PersistenceMechanics.CapacityPartitioning` (`global_budget`,
`count_lower_bound`, `bounded_backlog_zero_drift`, `service_balance`); its
machine instance is `CapacityLedger`. One ring offers 43 exchange opportunities
per period, so at most 43 protocols share a ring (`ring_protocol_bound`), or
`43 − R` with a Margin reserve `R` (`ring_protocol_bound_reserve`).

Impedance Matching is `PersistenceMechanics.ImpedanceMatching` (`ledger`,
`admissible_iff_transmission`, `zero_reserve_matched`, `realize`), with machine
instance `ImpedanceLedger`. The converter's flip `flag x = sin²(x/2)` is the
reflected fraction `r²`, and its pass probability is the transmission
(`converter_is_interface`, `converter_ledger`). The equivalent interface has
source `1 − s` and load `1 + s`, `s = |sin(x/2)|`; `x = π` is total reflection.
Over a period, reflected plus transmitted load is the number of encounters
(`period_ledger`); zero reserve registers nothing
(`zero_reserve_no_registration`), so a Toll-floor protocol needs positive
reserve (`toll_needs_reserve`).

Reversible Encoding is `PersistenceMechanics.ReversibleEncoding`, with instance
`PMElementaryParticles.RecordEncoding`. The paper's relational form keeps values
relative to a reference `x_o` together with `x_o` itself, because dropping the
reference merges distinct constant configurations. The record `labelRecord` merges labels:
six per colour class and two per lepton class (`record_fibers`), so the record
alone is not reversible (`record_not_injective`). The packet channel code is
reversible metadata (`packet_encoding_injective`), so Rule 2 holds inside the
packet and no external colour store is needed; any reversible metadata has at
least six states (`metadata_lower_bound`). The record comparator is colour-blind
(`bitToll_colour_blind`).

The colour reference is one site state, not the set `{e₁,e₂,e₃}`. The bit-level record
compares the lepton-axis bit and the sign bit; the colour-symmetric state
`(0,1,1,1)` has the colour record (`colourSymmetric_lepton_axis`,
`colourSymmetric_positive`) and is fixed by every colour permutation
(`colourSymmetric_invariant`). Hence colour does not force composites, no
partial comparison angle `1/√3` enters (`colour_axis_overlap`), and the vacuum
question reopens: in the colour vacuum up fails Map; in the lepton vacuum the
neutrino does.

`k` protocols on one 43-ring share the clock and the vacuum `+2e₀`, each with
its own packet. The firing pattern is joint, and Toll adds over packets
(`record_step_identity` per ring).

## Generations on the E8 wire

`EPLabelGen` places the labels on each wall for the three glue generations. `ControlledGluedRegister` gives the typed carrier routes. The glue address identifies a channel of transport. The occupancy-cost reading requires the occupied resources of a full recurring program at each address.

## Occupancy footprints

See the [whole-count occupancy table](../PMSubstrate/OVERVIEW.md#occupancy-footprints) for the counts, residuals and their shares.

## Mass readings in the tree

PM means the calculation is proved from the stated PM model. Scope refers to the named premises in [SCOPE](../../SCOPE.md#named-premises). Supplied means that the definition or its physical interpretation still takes an input. An indirect e8p read uses the result in another reported value.

This table includes the accounting used for occupancy cost. It also records retained operators, declared ledger values and decay formulas required by other consumers. The occupancy cost is the EP derivation under development.

### Retained carrier operators and constants

| Lean name | What it computes | Inputs it takes | Input status | e8p reads it | Relation to another row |
| --- | --- | --- | --- | --- | --- |
| `PMAction.DetunedWire.detunedWireOperator` | Complex weighted generation-wire matrix | Detuning and transfers on both walls | Supplied carrier parameters. | No direct read | DetunedWire.det_detunedWireOperator gives its determinant. |
| `PMAction.CompositeSchur.composite_schur_blocks` | Zero-energy light blocks, D₂Y⁻¹D₁† and adjoint | Crossing matrix Y and flips on both walls | Supplied blocks. Invertibility is needed for the physical Schur reduction. | No | WallSeesaw.effective_light_block is the equal-scalar-flip case. GappedGluedCrossing.occupied_light_mass specializes by label. |
| `PMAction.WallSeesaw.light` | Light Dirac matrix δ²Y⁻¹ | Detuning δ and gapped link Y | Supplied carrier parameters. | No | `WallSeesaw.effective_light_block` and `WallSeesaw.seesaw`. |
| `PMAction.WallDispersion.heavyGapSq` | Heavy squared rest mass of the one-flavour model | δ and y | Supplied carrier parameters. | No | WallDispersion.branch_gap_squares and two_dirac_particles. |
| `PMAction.WallDispersion.lightGapSq` | Light squared rest mass of the one-flavour model | δ and y | Supplied carrier parameters. | No | WallDispersion.branch_gap_squares and two_dirac_particles. |
| `PMAction.DetuningGap.lightGap` | Light spectral gap at unit link gap | δ | Supplied detuning. PM diagonalization. | Yes, via fermion-law checks | FermionMassLaw.massA_detuning and massB_detuning. |
| `PMConstants.FermionMassLaw.massA` | Unit-gap mass with δ² = yv | y and v | Scope VEV structure. Supplied mass identification. | Yes, FermionLawPulls | massA_detuning. |
| `PMConstants.FermionMassLaw.massB` | Unit-gap mass with δ = yv | y and v | Scope VEV structure. Supplied mass identification. | Yes, FermionLawPulls | massB_detuning. |
| `CarrierSpecies.CarrierSpecies.mass` | Electron and massless neutrino values in electron units | Species tag | Scope physical species mapping. Supplied massless approximation. | No | electron_mass and neutrino_mass evaluate the map. |
| `SubstrateBridge.normMass` | Half the E8 norm squared | Lattice vector z | PM lattice form. Species readout supplied. | No | Used by SubstrateBridge.widthCandidate. |
| `PMSubstrate.SIUnits.electronMassMeV` | Electron unit in MeV | SI units and E8 calibration | PM calibration formula. External SI unit convention and anchors. | Yes, through SharedUnits.me | QuarkMasses value enclosures use this unit. |
| `PMConstants.Bulk.floorMass` | Neutrino mass floor candidate | Coupling and electron unit | PM bulk index. Supplied particle interpretation. | Yes, floor comparison | FloorNeutrino.floor_bounds. |
| `PMConstants.FloorNeutrino.towerMass` | Inverse-period neutrino mass candidate | Base, scale and tier | PM Δ. Supplied base, scale and tier interpretation. | No | no_moderate_gap_ratio. |
| `PMConstants.GaugeSpectrum.wMassSquared` | Charged vector-boson squared mass | Coupling; substrate scalar and gauge inputs | PM arithmetic. Scope link transport and current normalization. | Yes | Used in TauLifetimeCorrected.wSq. |
| `PMConstants.GaugeSpectrum.zMassSquared` | Neutral vector-boson squared mass | Coupling; substrate scalar and gauge inputs | PM arithmetic. Scope link transport and current normalization. | Yes | GaugeSpectrum gives the neutral spectrum. |
| `PMConstants.ElectroweakE8.higgsMass` | Scalar mass from gain and VEV | Coupling and electron scale | PM gain arithmetic. Scope VEV structure. | Yes, through PMConstants.Values | VevDownstream.vev_downstream. |
| `PMConstants.ScalarSector.higgsSq` | Scalar squared mass at a supplied Fermi coupling | Fermi coupling | PM self-coupling; experimental coupling in e8p. | Yes, ScalarAccounting | E8PConstants.VevWindow.higgs_from_fermi bounds its square root. |

| `NeutrinoContext.mRest` | The bulk floor at the E8 coupling and electron unit. | E8 constants and the free-streaming mass identification. | PM floor arithmetic. Supplied identification. The measured splitting appears in the legacy comparison theorems. | Indirect. e8p uses the upstream floor. | It is a specialization of `Bulk.floorMass`. |
| `PMConstants.WMassTest.wMass` | W mass at a supplied Z scale. | Z mass and clock ratio. | PM clock ratio. Supplied Z scale and mass-angle identification. | Comparison | Conditional W/Z mass reading. |
| `PMConstants.ReadoutAccounting.rawWMass` | Occupancy-weighted W mass diagnostic. | Z mass and raw weak-angle count. | PM count. Supplied Z scale and occupancy identification. | Comparison | Conditional W/Z mass reading. |
| `PMConstants.SharedReference.quarkWMass` | Coloured-reference W mass diagnostic. | Z mass and quark-reference ratio. | PM count. Supplied Z scale and selected reference. | Comparison | Conditional W/Z mass reading. |

### Tier and species ledgers

| Lean name | What it computes | Inputs it takes | Input status | e8p reads it | Relation to another row |
| --- | --- | --- | --- | --- | --- |
| `TierLedger.upTiers` | Up tier list 0, 2, 3 | Declared order | Scope tier sets. | No | tiersFor .up by definition. |
| `TierLedger.downTiers` | Down tier list 0, 1, 2 | Declared order | Scope tier sets. | No | tiersFor .down by definition. |
| `TierLedger.electronTiers` | Electron tier list 0, 1, 2 | Declared order | Scope tier sets. | No | Electron branch of tiersFor. |
| `TierLedger.neutrinoTiers` | Neutrino tier list 0, 1, 2 | Declared order | Scope tier sets. | No | Neutrino branch of tiersFor. |
| `TierLedger.tiersFor` | Tier list by base protocol | Protocol tag | Scope tier sets. | No | List length lemmas give three entries. |
| `TierLedger.wireTier` | Tier at a protocol and a wire address | Address-to-tier map | Supplied map. Scope tier sets do not fix it. | No | Used in TransportCandidates.tier. |
| `LeptonMasses.muonFeedback` | Muon's geometric feedback term | E8 χ, σ and α | PM inputs. Supplied choice of term. | Indirect via muon | muonFeedback_fixpoint. |
| `LeptonMasses.muon` | Muon ledger mass / mₑ | E8 invariants, α and chosen ledger costs | PM invariants. Scope tiers and declared costs. | Yes, EP Values | muon_ledger; used by muonWidth and declaredMass. |
| `LeptonMasses.tau` | Tau ledger mass / mₑ | E8 invariants and chosen ledger costs | PM invariants. Scope tiers and declared costs. | Yes, EP Values | tau_ledger; tau_value = 3477. |
| `QuarkMasses.up` | Point-tier up mass / mₑ | D and overhead η | PM constants. Scope assignment and declared formula. | Yes, EP Values | up_ledger. |
| `QuarkMasses.down` | Point-tier down mass / mₑ | D, σ and η | PM constants. Scope assignment and declared formula. | Yes, EP Values | down_ledger. |
| `QuarkMasses.strange` | Line-tier strange mass / mₑ | D, Δ, χ, σ and η | PM constants. Scope assignment and declared formula. | Yes, EP Values | strange_ledger. |
| `QuarkMasses.charm` | Area-tier charm mass / mₑ | D, Δ, σ, χ and η | PM constants. Scope assignment and declared formula. | Yes, EP Values | threshold_match equates it to StrongRunning.mCharm. |
| `QuarkMasses.bottom` | Area-tier bottom mass / mₑ | D, Δ, χ, σ and η | PM constants. Scope assignment and declared formula. | Yes, EP Values | threshold_match equates it to StrongRunning.mBottom. |
| `QuarkMasses.top` | Volume-tier top mass / mₑ | D and Δ | PM constants. Scope assignment and declared formula. | Yes, EP Values | top_ledger. |
| `PMConstants.StrongRunning.mCharm` | Charm threshold in electron units | E8 area-tier constants | PM arithmetic. Declared species formula. | Indirect via strong running | QuarkMasses.threshold_match. |
| `PMConstants.StrongRunning.mBottom` | Bottom threshold in electron units | E8 area-tier constants | PM arithmetic. Declared species formula. | Indirect via strong running | QuarkMasses.threshold_match. |
| `PMConstants.StrongRunning.mTau` | Tau threshold in electron units | E8 area-tier constants | PM arithmetic. Declared species formula. | Indirect via strong running | Same arithmetic as LeptonMasses.tau. No named equality found. |
| `PMConstants.StrongRunning.mZ` | Z reference scale in electron units | 91,187.6 MeV and electron unit | Experimental Z input in running model. | Indirect via strong running | Separate from GaugeSpectrum.zMassSquared. |
| `TransportCandidates.declaredMass` | Optional table mass at a protocol and tier | Protocol, tier and ledger masses | Scope tiers and declared formulas. | No | Uses LeptonMasses and QuarkMasses by definition. |
| `TransportCandidates.mass` | Optional ledger mass at a wire address | Candidate and address-to-tier map | Supplied map and declared ledger mass. | No | Composes declaredMass with tier by definition. |

### Trial rates and capacity claims

| Lean name | What it computes | Inputs it takes | Input status | e8p reads it | Relation to another row |
| --- | --- | --- | --- | --- | --- |
| `PMAction.EventAccounting.cost` | Weighted event cost on a finite frame | Events, weights and unit Toll | Scope booked traffic and tariff. PM sum rule. | No | weighted_linear. |
| `PMAction.CommonResponse.responseCost` | Flag-weighted cost of repeated work | Unit price, work count and flag | Scope work and tariff. PM product rule. | No | common_normalization. |
| `PMAction.CommonResponse.bookedCapacity` | Sum of capacity times flag at booked visits | Visits, capacity and flags | Scope booking and tariff. PM sum rule. | No | booked_capacity_union and booked_capacity_const. |
| `PMKAutomaton.Values.mixedReceiverRate` | Booked mixed flags divided by 43 | AND/OR choice and booked slots | PM flags and period. Scope booking/pricing. | No | mixedReceiverRate_and, mixedReceiverRate_or and TransportCandidates.allBookedMixedRate_eq. |
| `PMKAutomaton.Values.equal_normalization_rate` | Serial rate ratio 1/2 or 3/8 | Common area, conversion, tick and quarter-time. Short or long path. | PM duration arithmetic. Scope common normalization and serial admission. | No | CertainTransferRate.common_tick_rate_ratio. |
| `ProgramWitness.registrations` | One bit-ring's registrations per frame | Program, reference, start and bit | PM ring flags. Scope physical program identification. | No | `ProgramWitness.witness_total` and `EPSpine.witnessAt_registrations`. |
| `ElectricPrimitiveToll.forwardToll` | Short writer flag sum | Channel and booked primitive comparison rule | PM decoder and flag calculation. Scope physical admission. | No | `ElectricPrimitiveToll.forward_tolls`. |
| `ElectricChiralKick.swapToll` | Shared-current swap flag | Channel and prepared carrier | PM flag for supplied state. Scope physical preparation. | No | Part of ElectricChiralKick.totalToll. |
| `ElectricChiralKick.totalToll` | Shared-current writer flags | Channel and prepared bank | PM path arithmetic. Scope physical current and booking. | No | `ElectricChiralKick.total_tolls`. |
| `HeavyFlipRecords.pairedToll` | Sum of active and static heavy-record flags. | Two carrier labels. | PM comparison under the supplied record. | No | `paired_tolls`. |
| `HeavyFlipRecords.orbitRecordToll` | Per-label heavy record flag count. | Carrier label and reference rule. | PM flag count. Scope heavy record contract. | No | `orbit_record_tolls`. |
| `ElectricFourPortRecord.exposureToll` | Two electric comparison flags. | Label on the four-port writer. | PM flags. Scope writer admission. | No | `exposure_tolls`. |
| `ElectricFourPortRecord.decodeToll` | Decoder flag subtotal for one port. | Port and decoder circuit. | PM circuit flags. Scope decoder admission. | No | Used by `ElectricFourPortRecord.forwardToll`. |
| `ElectricFourPortRecord.forwardToll` | Four-port exposure and decoder flag subtotal. | Label and canonicalization choice. | PM circuit flags. Scope writer admission. | No | `ElectricFourPortRecord.forward_tolls`. |
| `ProtocolToll.eventToll` | Sum of gate prices along a word. | Gate word, initial label and prices. | PM recursion. Scope tariff and physical word. | No | `eventToll_weak_partners`. |
| `ProtocolToll.survivalToll` | Two weighted selector tests. | Two weights and label. | PM flags. Scope tariff and test admission. | No | `survivalToll_differences`, `selector_half_flag_weight_iff`. |
| `WireSchedule.bitToll` | Two output flags for one writer reference. | Polarity and channel. | PM record arithmetic. Scope writer reference. | No | Used by `WireSchedule.polarityCost`. |
| `WireReferenceCost.factorFlagToll` | Two measured factor flags for the scheduled record. | Polarity and label. | PM flag arithmetic. Scope record reference. | No | `factorFlagToll_eq` relates it to `WireSchedule.bitToll`. |
| `WireSchedule.knownToll` | Subtotal of proved flags on paid visits. | Schedule, label and setup choice. | PM known flags. Scope booking. | No | `WireSchedule.fullToll` adds a supplied remainder. |
| `WireSchedule.fullToll` | Booked writer and remaining route cost | Schedule, setup and unpriced-visit functional | Scope admissibility and tariff. PM accounting. | No | WireSchedule.best_survival_iff relates minimizing cost to survival. |
| `WireSchedule.polarityCost` | Writer record cost by polarity | Address, species traffic and other cost | Scope population and lifecycle prices. PM book comparison. | No | polarity_cost_difference. |
| `TransportCandidates.allBookedMixedRate` | Mixed fixture rate at full booking | AND/OR candidate | PM on fixture. Scope physical booking. | No | allBookedMixedRate_eq. |
| `TransportCandidates.uniformTraceRegistrations` | Flags from uniform requests through the chosen trace | Rule, state and uniform request | PM count. Scope physical traffic. | No | uniformTraceRegistrations_zero. |
| `PMAction.RootTransferAccounting.gibbsRate` | Gibbs-selected trial probability per opportunity | Hazard and charged trial cost | Scope work and tariff. Supplied Gibbs selection for physical trials. | No | actual_rate_freedom leaves the physical trial rate open. |

### Decay widths and rates

| Lean name | What it computes | Inputs it takes | Input status | e8p reads it | Relation to another row |
| --- | --- | --- | --- | --- | --- |
| `RateModel.channelCost` | Expected per-frame event cost | Event family and unit Toll | Scope family and price. PM expected cost. | No | channelCost_eq. |
| `RateModel.channelRate` | Hazard times channel cost | Event family, Toll and hazard | Scope physical channel and HazardForm inputs. PM formula. | No | channelRate_eq. |
| `PMElementaryParticles.persistenceRate` | Hazard times cost rate | Hazard coefficient and cost rate | Scope HazardForm and physical cost. | No | survival_from_persistence and DecayLaw.rate_eq_pillars. |
| `PersistenceMechanics.Rates.parallelRate` | Sum of channel rates | Channel rate list | Supplied rates. PM additive rule. | No | MeanLife laws for total survival. |
| `BetaLattice.betaLatticeCost` | Cost of selected finite modes | Mode counts and unit Toll | PM count formula. Scope physical modes and price. | No | betaLatticeRate uses this cost. |
| `BetaLattice.betaLatticeRate` | Uniform-mode lattice rate | Active/total counts, hazard and Toll | PM formula. Scope physical active modes and hazard. | No | LeptonLattice reuses the finite channel. |
| `BetaLattice.betaWeightedRate` | Weighted finite-mode rate | Weights, active modes, hazard and Toll | Scope physical weights, hazard and tariff. | No | betaWeightedRate_le. |
| `BetaLattice.betaSpectralRate` | Exponential-weight finite cube rate | Cube, active modes, hazard and Toll | PM spectrum. Supplied weighting choice and Scope hazard. | No | Uses betaWeightedRate. |
| `BetaLattice.betaSpectralRateCutoff` | Spectrum rate with an energy cutoff | Cube, cutoff, hazard and Toll | PM spectrum. Scope physical cutoff and hazard. | Indirect via finite muon | betaSpectralRateCutoff_eq_one_of_openModes_eq_univ. |
| `LeptonLattice.leptonLatticeRate` | Finite lepton channel rate | Lepton channel, Toll and hazard | Scope physical channel and hazard. PM finite counting. | No | Reuses BetaLattice. |
| `PMElementaryParticles.muonFiniteWidth` | Finite-channel multiplier times muon width | Minimal cube and ledger muon mass | PM all-modes-open check. Scope physical mode and mass assignments. | Yes, via finite lifetime | muonFiniteWidth_eq. |
| `MuonRate.rate` | Massless-daughter differential rate | Contact strength, parent mass and daughter energy | PM integration. Scope V−A contact, flux and species readout. | Indirect via muon width | muon_rate; MassiveDaughterSpectrum.massless. |
| `MassiveDaughterSpectrum.rate` | Massive charged-daughter differential rate | Contact strength, parent/daughter masses and energy | PM phase space. Scope contact and physical masses. | Indirect via corrected lifetime | massless. |
| `MassiveDaughterSpectrum.width` | Integrated massive-daughter contact width | Contact strength and both masses | Same as its rate. | Indirect via corrected lifetime | massless_width and MassiveWidth.closed_width. |
| `PairInvariantSpectrum.massiveContactRate` | Differential rate with three massive final states | Contact strength, masses and charged-daughter energy | PM kinematic contraction. Scope contact and physical masses. | No | massiveContactRate_massless_pair. |
| `PairInvariantSpectrum.massiveContactWidth` | Integral of massiveContactRate | Contact strength and all masses | Same as its rate. | No | massiveContactWidth_massless_pair. |
| `PairInvariantSpectrum.rate` | Rate in the pair invariant for a massless pair | Contact strength, parent/daughter masses and pair invariant | PM change of variables. Scope physical channel. | No | integrated_rate. |
| `MassScaling.weakWidth` | Generic coefficient times G²m⁵ | Coefficient, coupling and mass | PM scaling under the dimension assumptions. Supplied coefficient and mass. | No | MassScaling.combined_scaling. |
| `SubstrateBridge.widthCandidate` | Power of the lattice norm mass | Power and lattice vector | PM mass expression. Supplied power and species readout. | No | symmetry_and_reference_do_not_select_fifth. |
| `ScalingObligations.width` | Parametric scaling of a decay width | Scaling exponents and normalization | Supplied scaling inputs; PM conditional exponent arithmetic. | No | Used in the scaling obligations. |
| `Widths.referenceWidth` | Rescaled reference partial width | Base width, mass ratio, mixing, channels and phase | Supplied physical inputs. PM product rule. | No | reference_width_pos. |
| `Widths.total` | Sum of channel widths | Finite channel widths | Supplied channels. PM sum. | No | identical_channels. |
| `SubstrateTransition.partialWidth` | Squared channel amplitude times phase | Transition system and final state | Scope physical operator and phase. PM evaluation. | No | partialWidth_zero_of_not_decay. |
| `SubstrateTransition.totalWidth` | Sum of allowed partial widths | Transition system and initial state | Scope physical final-state readout. | No | CarrierTransitionOperator.muonOperatorSystem_totalWidth and tauOperatorSystem_totalWidth. |
| `TopTransition.topRate` | Squared top transition amplitude times phase | Top amplitude and supplied phase | PM channel operator. Scope phase and physical contact. | No | topRate_nonneg. |
| `MuonLifetime.muonWidth` | Tree muon width in electron units | E8 Fermi coupling, ledger muon mass and contact model | PM integration and E8 constants. Scope VEV, mass ledger and contact. | Yes, via lifetime | muonWidth_eq_integral, muonWidth_eq_E8 and PMElementaryParticles.muonFiniteWidth_eq. |
| `RadiativeCorrection.correctedRate` | Tree rate times radiative factor | Tree rate and correction | Supplied correction. SM when used for QED. | Indirect via lifetime where used | Correction factor is explicit. |
| `MuonLifetime.muonLifetime` | Inverse tree muon width | Tree width | Inherits muonWidth. | Yes, as a natural unit | muonLifetime_eq and muonFiniteLifetime_eq_continuum. |
| `PMElementaryParticles.muonFiniteLifetime` | Inverse finite-cube muon width | Finite width | Inherits muonFiniteWidth. | Yes, EP Values | muonFiniteLifetime_eq_continuum. |
| `MuonLifetimeCorrected.muonLifetimeCorrected` | Muon lifetime with massive phase space and one-loop QED | Tree lifetime, phase factor and one-loop coefficient | PM phase factor. Supplied SM QED term. | Proof bounds available through EP Values | corrected_bounds. |
| `MuonLifetimeHigherOrder.lifetime` | Muon lifetime with higher QED corrections | E8 tree rate and supplied QED series | PM tree formula. Supplied SM QED coefficients. | Yes, Values.muonLifetimeFull | lifetime_bounds. |
| `TauLifetime.tauLife` | Tree tau lifetime from a muon reference | Ledger masses, measured muon lifetime and Bₑ | PM mass arithmetic. Declared ledgers and experimental values. | Yes, tau comparisons | TauE8.tauLifetimeE8_relation. |
| `TauE8.tauLifetimeE8` | Tree tau lifetime from E8-input muon rate | Tree muon lifetime, ledger masses and Bₑ | PM tree and mass arithmetic. Declared ledgers and experimental Bₑ. | Yes, EP Values | tauLifetimeE8_relation. |
| `TauLifetimeCorrected.tauLifeCorrected` | Tau lifetime with phase, W propagator and QED corrections | Tree benchmark, E8 W mass and electron and tau running α | PM phase and E8 W mass. Supplied SM corrections, α(mτ) and experimental tree inputs. | Yes, Values.tauLifetimeCorrectedFs | tau_lifetime_corrected. |

## EP premise ledger

Read the shared statements in [SCOPE, Named premises](../../SCOPE.md#named-premises).
The names in this table identify the rows by the Lean module in SCOPE's
“Where it enters in Lean” column. Local inputs below give the remaining
choice and the first layer that needs it.

| Layer | Lean location or SCOPE row | Status |
| --- | --- | --- |
| Substrate | SCOPE · `ClockAlignment` | Named placement premise. `alignedSectorBasis_eq` checks the explicit placement. |
| Substrate | SCOPE · Lorentzian signature and complex amplitudes | Named model premises. Root moments through degree four are PM theorems. |
| Substrate | `ChannelPlacement.channelE8`, `referenceClass_eq_clock` | Proved from PM. |
| Substrate | `SharedUnits.αe`, `SharedUnits.fermiME` | PM coupling and conversion formulas. The Fermi value inherits the SCOPE VEV structure. |
| Substrate | `SharedUnits.me`, `PhysicalUnits.electronTime` | PM conversion at the external SI unit anchors. |
| Node | SCOPE · `ClockSites`, `RingReceiver.tick` | Named tick-to-root identification. The finite clock and ring movement are checked. |
| Node | SCOPE · `ClockTickWeights`, `Machine.SliceHop` | Named closure premise. The discrete orbits are checked. |
| Node | SCOPE · `PMKAutomaton.Interface` | Named admission, geometry, resources, booking, traffic and tariff inputs. See the [upstream closeout](../PMKAutomaton/COMPONENTS.md#kautomaton-closeout). |
| Node | `CommonResponse.bookedCapacity` | PM sum rules. Local capacity values, distinct paid events and their common unit are supplied under SCOPE's machine-input row. |
| Carrier | SCOPE · `CarrierRepresentation`, triality to vector | Named carrier premise. |
| Carrier | SCOPE · `CarrierRepresentation`, sign index | Named carrier premise. |
| Carrier | SCOPE · `CarrierRepresentation`, reserved lepton axis | Named carrier premise. |
| Carrier | SCOPE · `Hypercharge`, `RequirementTable` | Named representation inventory with a sterile singlet. |
| Carrier | `CarrierRepresentation.carrierCharges_eq_standard` | Charge equality follows in Lean from the three carrier premises. The standard table is a comparison target for this result. |
| Carrier | SCOPE · `PacketGaugeActions` | Named weak `SU(2)` action on the sign pair. Colour and the hypercharge direction follow from PM under the carrier premises. |
| Carrier | SCOPE · `GeneratorNormalization` | Named stiffness normalization, inherited through the weak couplings. |
| Carrier | SCOPE · `LinkMass` | Named transport form. The link charge is derived. |
| Carrier | SCOPE · `HeavyFlipControl`, `ElectricCompanionBank`, `ElectricChiralKick` | Named heavy record and occupied companion contract. The typed guard action is proved. |
| Carrier | `VacuumLabel`, `refRecord`, `SharedReference`, `ColourReference` | Physical vacuum, sector and readout choice are open. |
| Carrier | `CompositeSchur` | Gapped crossing and flip coefficients are supplied. A booked execution must realize the coherent blocks. |
| Carrier | SCOPE · `ChargedInsertion`, `ResonanceLift` | Named offset and matched-port admission. Persistence of the calibration channel is open. |
| Carrier | `FermionMassLaw.massA`, `FermionMassLaw.massB` | Supplied alternatives for matching `yv` to detuning. The `κ_τ` measurement is an e8p comparison. |
| Protocol | SCOPE · `WireSchedule.Premises` | Named serial route and admitted bookings. |
| Protocol | SCOPE · `WireReferenceCost`, `PMKAutomaton.Values` | Named population and reset contract. The threshold arithmetic is proved. |
| Protocol | `EPSpine.spine`, `EPSpine.witnessAt_registrations` | Proved for class witnesses. Closure of a complete occupied program is open. |
| Protocol | SCOPE · `TierLedger.tiersFor` | Named tier lists. The wire address assignment remains an explicit input. |
| Protocol | `LeptonMasses.muon`, `LeptonMasses.tau` | Declared geometric cost formulas. The invariant values and arithmetic follow from PM. |
| Protocol | `QuarkMasses.up` through `QuarkMasses.top` | Declared species cost formulas. The invariant values and arithmetic follow from PM. |
| Protocol | `KoideSelection.generationLaw` | Named local generation-record premise. Koide follows with selection on that law. |
| Protocol | `KoideSplit.circulant_koide` | The split is proved for supplied amplitudes. Phase and relation to an occupied trace are open. |
| Protocol | SCOPE · `ExternalStates`, `NativeExternal` | Named physical species and decay/current readout. |
| Protocol | `CarrierAmplitude`, `CarrierTransitionOperator` | Supplied coupling assignment and link from the operator to physical external states. |
| Protocol | `ProtocolDynamics`, `RateModel` | Decay relation and finite accounting are proved. Physical histories and their event rates are supplied. |
| Protocol | `MuonRate.parentFlux`, `WExchangeRate` | Supplied relativistic flux and physical V−A/weak contact identification. The kinematic and zero-transfer formulas are proved. |
| Protocol | `PolarMeasure`, `PairSphere`, `LeptonLattice` | Measures and finite counting are proved. The support and scale choice for the physical final state are supplied. |
| Protocol | SCOPE · `HazardForm`, `MeanLife` | Named persistence-law inputs. |
| Protocol | SCOPE · Born rule and `InclusiveMixing` | Named probability interpretation where amplitude-derived channel weights are used. |
| Protocol | `MuonLifetimeCorrected`, `MuonQEDLoops` | SM QED coefficients and correction expansion supplied. |
| Protocol | `TauLifetime.tauLife`, `TauE8.tauLifetimeE8` | Experimental muon lifetime and branching fraction for the first. Experimental branching fraction for the second. |
| Protocol | `TauLifetimeCorrected.qedTau` | SM radiative formula with supplied `α(m_τ)⁻¹ = 133.3`. |
| Protocol | `TauLifetimeCorrected.wRatio` | SM finite-propagator correction applied with the E8 W mass. |

## Lean modules changed since 37e9cce

The table lists the modules from the earlier audit that remain in the tree.

| Lean module | What it certifies | Supplied input before a physical number |
| --- | --- | --- |
| `PMAction.CommonResponse` | Adds capacity times flag over disjoint booked visits. | Complete visit set and physical capacity and flag values. |
| `PMElementaryParticles.EPLabelGen` | Reindexes each wall by generation and attaches invariant labels to the spine. | Physical occupied execution and its prices. |
| `PMElementaryParticles.ElectricCoordinateDecoder` | Certifies the short unitary writer and reversible coordinate preparation. | Admitted root pulses, elapsed ticks and occupied input bank. |
| `PMElementaryParticles.WireSchedule` | Checks serial route placement, conditional Toll and minimum-cost selection. | Physical admission, fresh supply, reset, traffic and tariffs. |
| `PMKAutomaton.RingReceiver` | Realizes the reversible receiver and the restored comparison probe. | Physical rule, requests, initial traffic and booking. |
| `PMElementaryParticles.KoideSplit` | Proves the norm-split form of the Koide ratio. | Physical generation record and Fourier phase. |
| `PMElementaryParticles.LeptonMasses` | Evaluates the declared lepton cost ledgers and muon feedback fixed point. | Physical derivation of the named ledger costs. The formulas already evaluate. |
| `PMElementaryParticles.PolarMeasure` | Constructs the radial and energy-shell phase-space measure. | Physical choice of scale, support, contact channel and masses. |
| `PMElementaryParticles.TierLedger` | Checks the declared three tiers for each base protocol. | Physical address-to-tier map and per-tier price. |

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
| `MeanLife` | `Rates.meanLife rate h` is the positive-rate reciprocal and survival integral; `persistenceRate = β·costRate`; `survival_from_persistence` | the three persistence premises of `HazardForm`; the cost rate and `β` |
| `RateModel` | `channelCost = expectedCost c0 E`; `channelRate_eq : rate = β·c0·Σ prob`; `channelMeanLife` uses `Rates.meanLife` at positive rate; zero-probability channels have zero rate | the event family per channel, and the toll/hazard coefficients |
| `BetaLattice` | `BetaLatticeChannel` (`modes`, `active`), `event`, `family`; `betaLatticeRate = β·c0·active/(modes+1)`, `betaLatticeLifetime`, positivity; `betaSpectralWeight = exp(−λ)`, `betaWeightedRate`, `betaSpectralRate`; `betaOpenModes`, `betaSpectralRateCutoff`, positivity, `betaWeightedRate_le`, `betaSpectralRateCutoff_le` (`rate ≤ β·c0`); general gap lemmas `dirichletEigenvalue_mono`, `dirichletEigenvalue_ge_next`, `betaOpenModes_eq_univ_of_twelve_le`, `betaOpenModes_eq_singleton_of_gap`, `betaSpectralRateCutoff_eq_one_of_openModes_eq_univ` | numerical spectral sum / neutron benchmark |
| `LeptonLattice` | finite lepton channel reusing `BetaLattice`; `leptonLatticeRate`, `leptonLatticeLifetime`, positivity | lepton eigenvalue input |
| `LeptonLifetime` | `muonSpectralFraction`, `muonFiniteWidth`, `muonFiniteLifetime`; minimal-cube lepton channel | mass/phase-space coefficient still continuum |

## Results of the 2026-11-16 review

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
