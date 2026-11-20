# PMElementaryParticles — overview of checked results

Why continuum phase space is correct on a lattice substrate, and when it is not: [`CONTINUOUS.md`](CONTINUOUS.md).

The single map of what Paper V proves and what later work can reuse. Open work is
in [`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md); build instructions are in
[`README.md`](README.md). Sources are under `PMElementaryParticles/`, imported by `PMElementaryParticles.lean`.
Theorem names are entry points, not exhaustive lists; the Lean source is ground
truth. Library order: PMSubstrate → PMAction → PMConstants → PMKAutomaton → PMElementaryParticles → PMFlavor → PMHadrons → PMAtoms → PMCosmology (`AuditDependencies`). This folder imports nothing from PMFlavor.

For the remaining physical inputs, see the [EP protocol blockers](REVIEW-AND-NEXT.md#protocol-readout-blockers).
The transport laws are exposed by the [conditional interface](../PMKAutomaton/COMPONENTS.md#kautomaton-closeout).

## EP persistence rebuild — structure

1. **Machine EP uses.** The certified machine is KAutomaton's conditional
   interface: `PMKAutomaton.Interface` for operations and
   `PMKAutomaton.Values` for conditional rates. The isolated-excitation sector
   is `IsolatedExcitation`/`IsolatedReceiverTrace`; the bit-ring machine is
   `RecordPortIdentification`; the phase-to-record converter and coin are
   `PhaseToRecord` and `CommonComparator`. KAutomaton keeps T, L, B, D, J, Q
   and the tariff unit as named machine inputs.
2. **Protocol definition.** `Protocol.Protocol` is finite data: one of the 16
   labels, a reference record, one firing pattern per record bit on the 3-ring,
   certified phases `{0,π}`, and one packet site. Its per-period receiver Toll
   is `Protocol.receiverToll`.
3. **Pillar conditions.** `PillarPredicates` defines the weakest paper
   predicates on `Protocol`, with named variants for Margin, Map and Toll, and
   links each to `Requirements.Pillar.requirement`.
4. **Enumeration.** `Protocol.allProtocols` is the complete finite family of
   16 labels × 2 references × firing patterns × certified phases × packet site
   (`allProtocols_complete`). `PillarPredicates.survivors` filters it by the
   six predicates. A direct `decide` over all 24,576 protocols exceeded 600
   seconds; survivor counts are evaluation observations, not kernel proofs.
5. **Legacy results and status.** The old species, tier, generation and
   heavy-label material is retained as a legacy ledger. Its status is audited
   in the section below and is not derived by this rebuild unless explicitly
   stated.

### Pillar availability and enumeration outcome (Tasks 2–5)

`PersistenceMechanics.Requirements` supplies the three requirements, the six
pillar names, the requirement map, `Pillar.regulates` and `Pillar.sign`, plus
the abstract `PMRequirements`. It does **not** supply six individual physical
predicates on a machine state. The missing pieces are concrete predicates for
Capacity, Margin, Map, Protocol, Toll and Governor on `Protocol`. Without them
the six-pillar filter and the alone/together analysis cannot be performed
without inventing new definitions; that is the Task 2 stop.

`Protocol.allProtocols` is nevertheless complete
(`allProtocols_complete`): 16 labels × 2 references × 2^6 firing patterns ×
2^2 certified phases × 3 packet sites = 24,576 finite protocols. No protocol
is filtered. Grouped by `labelRecord` (reference choice doubles each):
`(false,false)` 6, `(false,true)` 6, `(true,true)` 2, `(true,false)` 2.
Reference groups are colour and lepton. Since no pillar predicate exists, no
3-ring result settles the filter; a larger ring is not the missing piece—the
missing piece is the predicate definition.

**Loop closure / Delta (Task 4).** No pillar predicate in `Requirements`
requires a state return within `Delta`. `RingReceiver` has a clock phase
`finRotate Delta`, and the bit-ring ports use `finRotate n`; no certified
theorem identifies the bit-ring position with the clock phase. The
“one firing site on the 43-ring gives one registration per period” statement
is therefore not certified here.

**Alone/together (Task 5).** Since the six predicates are missing, alone and
combined closure cannot be decided. The sharing lemmas
(`WireReferenceCost.shared_maintenance_free`, `SharedReference`,
`ColourReference`) remain available, but there is no predicate to satisfy and
no grouping is assumed.

**Legacy single-reference assumptions after P3.** The corrected least-Toll
reference is per label: up→lepton, down→colour, electron→lepton,
neutrino→colour. Consequently:

- `down_geometric_mean` was stated for the colour reference on all labels. Under
  the per-label least-Toll references the selected Tolls are
  `T_e = T_d = T_u = 1`, so the identity still holds numerically, but now as an
  equal-Toll case rather than the colour-row mean. It is not a universal
  single-reference statement.
- The record Toll rows `(2,1,0,1)` (colour) and `(1,2,1,0)` (lepton) remain
  valid per reference. Per-label selection takes one entry from each row
  (electron/up from lepton, down/neutrino from colour); neither row is the
  universal reference.
- The legacy heavy writer assumed one polarity/reference for all labels. That
  single-reference assumption is contradicted as universal. The heavy weight
  remains conditional per label; no single reference is selected for the
  heavy writer.

### Legacy audit (Task 6)

| Legacy result | Status | Reason / theorem |
| --- | --- | --- |
| 16-channel layout | Consistent premise | `ProtocolInventory.channels_card` etc. certify the stipulated inventory; the persistence rebuild uses it as the finite label set. Not derived from persistence. |
| `labelRecord` bits | Consistent premise at the physical record level | `HeavyFlipControl.labelRecord` is certified finite data and `bitToll_eq_hamming` reproduces the rows; no persistence derivation of the physical record identification. |
| Tier sets `{0,2,3}` / `{0,1,2}` | Consistent premise | `TierLedger.tiersFor` is a declared ledger; no address-to-tier theorem comes from the bit-ring machine. |
| `QuarkMasses` formulas | Consistent premise | E8 arithmetic is certified; formula-to-tier assignment is declared (`QuarkMasses` legacy audit status). |
| `LeptonMasses` formulas | Consistent premise | E8 arithmetic and feedback fixed point certified; tier assignment declared (`LeptonMasses` legacy audit status). |
| Generations as glue addresses `g±1` | Consistent premise | `GenerationWalls`, `GenerationOrientation`, `ControlledGluedRegister` certify the glue structure; no persistence derivation of the generation-to-mass assignment. |
| `down_geometric_mean` | Conditional/consistent | `HeavyFlipRecords.down_geometric_mean` holds for a common bit price and the colour reference; the reference is free and the mass reading is not derived. |
| Heavy-label weight | Undetermined | Depends on the free reference and on a firing requirement that is not certified (`bitRingTotal43_empty_zero`; Task 4). |
| Record Tolls `(2,1,0,1)` / `(1,2,1,0)` | Derived at the flag level / conditional physically | `bitToll_eq_hamming`, `colour_hamming`, `PhaseToRecord.bitToll_eq_expected_conversion`; physical record-port identification remains the admitted trace. |

**Filter-derived changes to the legacy audit.** The Map predicate now derives
reference exclusions per label: with Hamming ≥ 1, up-record labels are invalid
under the colour reference and neutrino-record labels under the lepton
reference; with Hamming = 2 only the complementary record pair survives. The
Toll predicate excludes empty firing, so the unconstrained least-Toll zero is
not a survivor once Toll is imposed. The Margin predicate excludes full firing
under the per-ring variant. Tier sets, generation addresses, quark/lepton
formulas and heavy-label weights are unchanged: the filter does not derive
them. Record Tolls remain derived at the flag level and conditional on the
physical record-port identification.

### Pillar predicate results (Tasks 1–5)

`PillarPredicates.lean` adds the weakest predicates from the PM paper:

- Capacity: `tollCount ≤ 2·43`.
- Margin:
  - `marginUtilization` — directly the paper's Fragility condition: every
    registering ring has period count `< 43`;
  - `marginPerRing` and `marginTotal` are retained only as named **proxies**:
    no ring full, and both rings not jointly full.
- Map variants: `mapAtLeastOne` (Hamming ≥ 1) and `mapBoth` (Hamming = 2).
- Protocol: `protocolPillar` is `True` on the finite data because the machine
  tick is reversible (`tick_bijective`) and both rings use the common `Fin 3`
  clock.
- Toll variants: `tollTotal` (period total ≥ 1) and `tollPerRing` (each
  differing ring ≥ 1).
- Governor: `governorProper` excludes the all-firing transition set.

Each predicate is linked by a `*_realizes_*` theorem to
`Requirements.Pillar.requirement`.

**Filter and quotient.** `SurvivorClasses.Reduced` quotients the raw label to
`labelRecord`; `satisfies_labelRecord_invariant` proves labels with the same
record are indistinguishable to every predicate when the other fields agree.
`survives_iff_reduced` identifies the raw filter with `SurvivorsR`. The raw
label multiplicities are 6 for `(false,false)`, 6 for `(false,true)`, 2 for
`(true,true)` and 2 for `(true,false)`. Reference, firing patterns, phases and
`x0` are read by at least one predicate; no further quotient is used.

Reduced survivor counts by variant `(marginPerRing, mapBoth, tollPerRing)` are
proved in `SurvivorClasses.survivorsR_cards`:

| variant | reduced survivors |
| --- | ---: |
| F,F,F | 2,352 |
| F,F,T | 1,608 |
| F,T,F | 1,032 |
| F,T,T | 288 |
| T,F,F | 1,800 |
| T,F,T | 1,224 |
| T,T,F | 792 |
| T,T,T | 216 |

The raw counts are these reduced counts times the label multiplicities; they
are not the primary result.

**Corrected Margin and robust core (Task P3).** `marginUtilization` replaces
the firing-site proxy for the robust calculation. Reduced survivor counts are
proved in `SurvivorClasses.survivorsU_cards`:

| `(marginUtilization, tollPerRing)` | reduced survivors |
| --- | ---: |
| total Toll | 1,650 |
| per-ring Toll | 1,110 |

The robust core `RobustCoreU` is the intersection of the total- and per-ring
Toll variants. A direct decide over the reduced intersection exceeded 600
seconds and was stopped; the intersection count, class table and minima below
are evaluation observations, while `survivorsU_cards` is the proved part. The
class table, with phase multiplicity included, is:

| record | reference | reduced survivors | period registration counts |
| --- | --- | ---: | --- |
| up `(false,false)` | lepton | 240 | 14,15,21,22 |
| up | colour | 0 | — |
| down `(false,true)` | colour | 240 | 14,15,21,22 |
| down | lepton | 75 | 28,29,30,35,36,37,42,43,44 |
| electron `(true,true)` | colour | 75 | 28,29,30,35,36,37,42,43,44 |
| electron | lepton | 240 | 14,15,21,22 |
| neutrino `(true,false)` | colour | 240 | 14,15,21,22 |
| neutrino | lepton | 0 | — |

**43 and 86.** The corrected Margin removes every single-ring 43 and the
two-ring 86. A total of 43 remains only as a two-ring sum, not as a ring at
utilization 1. The old `marginPerRing`/`marginTotal` proxy tables with 43/86
are retained as proxy history, not the corrected result.

**Least Toll per label.** On the corrected robust core:

| record | valid references | minimum Toll | least-Toll reference |
| --- | --- | ---: | --- |
| up | lepton | 14 | lepton |
| down | colour, lepton | 14, 28 | colour |
| electron | colour, lepton | 28, 14 | lepton |
| neutrino | colour | 14 | colour |

Each label reaches the same minimum rate, 14. The reference is unique for
up, neutrino and for the both-valid down/electron rows because the minima
differ.

**Reference per record class (corrected robust core).** Up is valid only with
the lepton reference; neutrino only with colour; down selects colour by least
Toll; electron selects lepton. `mapBoth` remains the stronger Map variant.

**Shared vs per-label reference (Task P4).** Step 0 is proved without a
decide: `satisfiesUtil_perRing_imp_total` gives
`RobustCoreU = SurvivorsU true` (`robustCoreU_eq`) and
`RobustCoreU.card = 1110` (`robustCoreU_card`).

The background question is **not certified**: outcome (c). The certified
two-sector facts are `Channels.e8_two_d4_sectors`, `Vacuum.sectors_are_d4`,
`CarrierVacuumSector`, `IndependentRegisters.sectorEquiv`,
`bitRingConfig_stationary`, `SharedReference`, `ColourReference` and
`GenerationWalls`. None identifies a bit-ring background with a specific E8
lattice or D4 sector, and none assigns the record classes (up/down/electron/
neutrino) to sectors. The missing object is a certified map from the abstract
`Fin 3` bit-ring background to the lattice background and a sector assignment
of record classes.

Conditional shared-reference tables from the corrected class table:

| shared vacuum | valid record classes | minima |
| --- | --- | --- |
| colour `(false,false)` | down, electron, neutrino | 14, 28, 14 |
| lepton `(true,false)` | up, down, electron | 14, 28, 14 |

Under one shared colour reference, **up** fails Map; under one shared lepton
reference, **neutrino** fails Map. No single shared vacuum is valid for all
four record classes. The P3 per-label least-Toll references
(up→lepton, down→colour, electron→lepton, neutrino→colour) are therefore
conditional on per-label backgrounds and are not certified while Step 1 is
(c).

**Legacy under shared reference.** With a shared colour vacuum the applicable
row is `(2,1,0,1)` for down/electron/neutrino and up is invalid; with a shared
lepton vacuum the row is `(1,2,1,0)` for up/down/electron and neutrino is
invalid. `down_geometric_mean` is then nontrivial: colour gives
`T_e,T_d,T_u = 2,1,invalid`; lepton gives `1,2,1`, where
`s_d² ≠ s_e s_u`. It does not hold nontrivially under either single vacuum.
The P3 per-label selection makes all three Tolls 1, so the identity holds only
as an equal-Toll special case. The heavy writer's single reference is
consistent only with a shared vacuum, which is not certified.

**Record coordinates and E8 placement (Task P5).** The lead is verified only at
the finite-code level. `RecordCoordinates.labelIndex_decomp` writes
`labelIndex c = 2*axis + sign`, and `labelRecord_eq_axis_sign` proves
`labelRecord c = (axis = 0, sign = 1)`. `channelCode_card` records the
`Bool × Fin 8` code: two walls × eight signed axes.

No certified theorem identifies `labelIndex` with the eight minimal vectors of
a specific `D₄` glue class. `Channels.minimal_class_card` proves each nontrivial
class has eight minimal vectors, and `Channels.nu_eq` counts 16 channels per
sector, but the bijection from `labelIndex`/`PacketGaugeActions.Channels` to a
sector and glue class is missing. Consequently the report does not certify that
all 16 channels lie in one D4 sector; the per-sector background option is not
excluded by the library.

Reference records are the coordinate pairs colour `(axis≠0, sign0)` and lepton
`(axis0, sign0)`. `SharedReference` supplies a reserved layout cell and
`ColourReference.colour_reference_in_payload` locates a colour reference in the
payload. Neither is proved equal to either `refRecord`; the missing object is a
map from the layout/payload reference to a minimal vector of the identified
class. Task P5 Step 2 is therefore outcome (c): the references exist as
objects but are not identifiable in the certified library.

No certified line in E8 carries the abstract `Fin 3` bit ring. `AxisHop`,
`NativePacketLinks`, `OpenHandoff`, `ReferenceClassHop` and `GenerationWalls`
certify qualified links/axis moves, but no theorem identifies a bit-ring
background with a root/axis line or a connected part of the lattice. The
missing map is the same placement map.

**Attachment to E8.** The finite record coordinate is
`labelRecord c = (axis=0, sign=1)` (`RecordCoordinates.labelRecord_eq_axis_sign`).
`ChannelVectors.channelCoord` is the full 16-channel map:

- active-false: `vectorCoord`, the vector-class minimal vector
  `sign·2e_axis`, with `vectorCoord_norm4 = 4`, `vectorCoord_glueClass = 1`;
- active-true: `spinorCoord`, the certified triality image of `vectorCoord`,
  with `channelCoord_glueClass = 2`.

`channelCoord_norm4`, `channelCoord_glueClass`, `channelCoord_injective`, and
`channelCoord_image_card = 16` prove the full map is an injection of the 16
channels onto the minimal vectors of two classes. The vector class is the
active-false class; the active-true class is the certified `c ↦ c+1` triality
image (`GluedRegister.triality_class`, `CarrierTriality.carrierTriality`). The
orientation is fixed by that convention, not chosen here.

Triality gives three attachments by applying `triality^0,1,2`; they are related
by the certified class shift. The two labelRecord bits are the signed-axis
coordinates in the vector attachment; in the spinor classes they index the
triality image, not a geometric signed axis. The attachment index is the glue
address/generation index (class 0 is the reference wall,
`HeavyFlipControl.direct`). No attachment is selected.

Under the vector attachment, lepton `refRecord false = (axis0,sign0)` is the
single vector `+2e_0`; colour `refRecord true = (axis≠0,sign0)` is the set
`{+2e_1,+2e_2,+2e_3}`. A single-site stationary background has one value
(`NativeReferenceBackground.stationary_iff`), so the lepton vector can be a
single-site background; the full colour reference cannot. It can only be
carried by a three-part composite of colour-axis vectors, using
`PacketGaugeActions.permuteColour`/`record_colour`, not by one site.
`SharedReference` and `ColourReference` remain layout/payload objects; neither
is proved equal to either reference. Outcome (c) remains.

In the lepton vacuum the neutrino record equals the vacuum vector and fails
Map; in the colour composite the up record is the reference record and fails
Map. Thus no single vacuum is valid for all four record classes.

No certified E8 line carries the abstract `Fin 3` bit ring. `AxisHop` proves an
axis step is two root events; `OpenHandoff` routes along a primitive root
direction, not the vacuum axis vector `2e_0`. The map from the bit ring to a
line through `+2e_0` is missing, so the lattice period/rate cannot replace the
3-ring registration counts. Those counts remain 3-ring artifacts.

Triality checks on the valid set cannot be completed without the bit-ring line
map and a chosen attachment. The reference wall and clock are the certified
triality-breaking structures; `crossing_word_glued` and the clock periods give
the extra work but no per-generation protocol cost here. Tier-ledger orders
`1/Δ`,`1/Δ²` remain observation only.

**Alone/together.** The nested-paper composition rules are Capacity
Partitioning, Reversible Encoding and Impedance Matching
(`PM-3-Nested/paper/2_nested_persistence.tex`). They are not a composition rule
on a single `Protocol`: no multi-protocol state with shared clock/reference,
capacity partition and interface overhead is defined in the library. The
composition question therefore stops at that missing definition; no SM grouping
or confinement is assumed.

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

**Certified coin and spectrum (Task L).** The converter's pass and flip
amplitudes are `(1 + e^{ix})/2` and `(1 - e^{ix})/2` (`converter_plus`,
`converter_minus`), i.e. `cos(x/2)` and `sin(x/2)` up to the common phase
`e^{ix/2}`. `encounter_unitary` gives the coherent one-site encounter. At
`x = π`, `exact_bit_flip` gives pass amplitude 0 and flip amplitude 1. The
full-firing ring script `tools/bit_ring_checkerboard.py` verifies the exact
block dispersion `cos E(k) = cos(x/2) cos k` to machine precision, with gap
`x` at `k=0`; empty firing is gapless. The Lean full-ring block proof was not
completed; the k=0 and exact-bit cases are certified. The mass reading of
this spectrum remains a hypothesis, not a result.

**Phase-to-record converter (Task K).** The certified comparator
`CoherentComparisonRepair.compare (InterferenceReadout.phase x)` is unitary
(`PhaseToRecord.converter_unitary`). On the phase-encoded input `phaseInput`,
the minus output has probability exactly `DiagonalReadout.flag x`
(`minus_probability`), and the expected receiver flag is `flag x`
(`expected_receiver_flag`). The converted branch records are orthogonal
(`converted_records_orthogonal`, `converted_branch_records_unequal`), and
`bitToll_eq_expected_conversion` recovers the EP row. The factor of two is the
phase encoding (`nsq/4`) versus orthogonal receiver encoding (`nsq/2`). Gap U's
flag identification closes for all phases; no new unitary was defined.

**Common comparator (Task J).** Receiver and electric flags share the
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

`IsolatedExcitation` defines the object a mass refers to: the stationary E8
reference (`Vacuum`/`RegisterVacuum`, `CarrierVacuumSector`, and
`NativeReferenceBackground.background_stationary`) plus one packet carrying a
single 16-slot label. `occupiedInput_valid` and `occupiedInput_admitted` prove
the two-bank occupancy; `occupiedInput_supply` and
`occupiedInput_acceptance` are the existing supply and acceptance results.
This is the definition of a mass, not a choice of O: occupancy is fixed at
vacuum plus one excitation. The vacuum is not unique; `vacuum_nonunique`
records the certified rest-mode family.

`IsolatedReceiverTrace` defines two port fields. `uniformPorts` puts the
packet on all three sites and both streams. That is **not one excitation**:
`uniformPorts_occupancy` counts six true bits when the packet is active, so it
fails the occupancy check. Its zero receiver flags (`uniform_flag_zero_AND`,
`uniform_flag_zero_OR`, `uniform_AND_OR_tie`) are equal-arrival artifacts of
that control field, not isolated-excitation results.

`localizedPorts x0 packet` is the one-excitation field: site `x0` has live
`active packet` and record vacuum (`false`), and every other live/record value
is vacuum. `localizedPorts_occupancy` gives one true bit when the packet is
active and zero otherwise; `localized_occupancy_preserved` proves this is
preserved by `RingReceiver.tick` under both rules. The phase, retained
requests and probe bits are the open controller fields G/T, named in
`ReceiverFields`.

The requests are retained (`localized_requests_retained`). The localized port
field has period 12 (`portStep_period_twelve`,
`localized_ports_period_twelve`), so the 43-tick sum is three full periods
plus seven ticks (`localizedSum43_eq`). The exact sum depends only on the
exchange pattern (`localizedSum43_eq_pattern`), with table
`patternSum` / `patternTable`. For pattern code 0…7 (q0 least significant,
entries for x0 = 0,1,2): `000→0,0,0`; `100→14,14,15`; `010→15,14,14`;
`110→43,21,22`; `001→14,15,14`; `101→21,22,43`; `011→22,43,21`;
`111→43,43,43`. AND and OR differ exactly when their pattern-table entries
differ (`localized_and_or_differ_iff`, `sumsDiffer`). Simultaneously rotating
the packet site and the request field leaves the sum unchanged
(`localizedSum43_rotate`), but for fixed requests the sum can depend on `x0`
(`localizedSum43_x0_depends`). An inactive packet gives zero
(`localizedSum43_inactive_zero`). The receiver column and the record
bit-visit column remain separate, with no certified common ledger.

**Finding.** Requests are independent initial data; no certified relation to
the reference background exists. `ClockedRootTrials` takes the controller
background and its request projection as separate inputs (`historyCount`);
`LocalController` and `RingReceiver` retain supplied requests; the native
background stores reference values, not requests. No map from the background
configuration to the request field is certified.

**Unconstrained least Toll.** For the localized one-packet 3-ring,
`localizedSum43_eq_zero_iff_empty` gives sum zero iff the exchange pattern has
no firing site. `localizedSum43_nonempty_ge_fourteen` gives every non-empty
pattern at least 14. Thus PM least Toll selects exactly the empty firing
pattern: `and_zero_iff_no_true_true` says AND selects request fields with no
site `(true,true)`; `or_zero_iff_all_false` says OR selects request fields
with every site `(false,false)`. The unconstrained isolated packet therefore
never registers at the receiver. On the 4-ring the same zero-iff-empty result
is `localizedSumN_four_zero_iff_empty`. The n=5 decide did not finish within
ten minutes; that run was stopped at n=4.

**Reference-background bit rings (Task I, hypothesis).** The candidate model
is the vacuum as reference record on both streams everywhere; a packet
replaces the live bits at one site by its label bits; each record bit
(sector, position) runs on its own ring with its own requests. The reference
records are colour `(false,false)` (up record) and lepton `(true,false)`
(neutrino record). `bitToll_eq_hamming` proves both EP rows equal the Hamming
distance; `colour_hamming` gives `orbitRecordToll`.

Complement symmetry: `tick_complement` and `receiverFlag_complement` for
general `n`. `bitRingEmbed` has ports `(refBit,refBit)` everywhere except live
`labelBit` at `x0`. If `labelBit = refBit`, `bitRingEmbed_equal_zero` gives
zero flags at every tick; the background alone is fixed
(`bitRingEmbed_background_fixed`). The bridge to
`NativeReferenceBackground.stationary_iff` is `bitRingConfig_stationary`
(constant native reference configuration on the connected ring) together with
`bitRingConfig_streams` and `bitRingPortBackground_fixed`; they agree on the
labelled stream cells. If the bits differ, the state is
`localizedEmbed` or its complement (`bitRingEmbed_false_true`,
`bitRingEmbed_true_false`), and `bitRingSum43_eq` gives the 43-tick sum as
`localizedSum43 either requests x0`.

Total over two bit-rings: `bitRingTotal43_eq`; with a shared firing pattern,
`bitRingTotal43_shared` gives `bitToll ref c * patternSum (firingPattern either r) x0`.
Least Toll (empty firing in both rings) gives total zero for every label
(`bitRingTotal43_empty_zero`); a label with zero Hamming distance registers
zero for every request field (`bitRingTotal43_hamming_zero`). This removes
the Task H encounter scaffolding; `encounterState` and
`identification_flag_total` were removed. The model is a hypothesis, not a
certified identification.

**Reference choice (Task 3, outcome c).** The reference stays a free choice.
`ColourReference.colour_reference_in_payload` locates a colour reference in
the payload; it does not select a writer record. `SharedReference` supplies one
reserved cell for weak/hypercharge layouts. Neither identifies the bit-ring
reference with a sector's zero-Toll record (colour up `(false,false)`, lepton
neutrino `(true,false)`). `vacuum_nonunique` indexes rest modes, not record bit
pairs. The choice enters exactly in `refRecord` / `bitRingEmbed refBit`.

**Firing requirement (Task 4, outcome b).** No certified result says an
excited bit must register again. `CoherentRefresh.minimum_once`,
`RefreshSchedule.minimal_is_ledger`, `ReferenceMaintenance`,
`RecordSupply.clean_supply`, `CoherentRecordRestoration.twice_undoes` and the
conservation requirements concern refresh, maintenance, restoration or
conserved occupation, not a lower bound on `receiverFlag`. The missing link is
the same gap U. No requirement was created.

**Checkerboard test (Task 5, hypothesis amplitude).** `tools/bit_ring_checkerboard.py`
models the two directions with a coin of angle `theta` at firing sites. It
finds the empty-firing ring gapless and the full-firing ring gapped, with gap
`theta` and a small-`k` Dirac-like fit `E^2 ≈ sin^2 k + (theta/2)^2`. This is a
script-level pass for the checkerboard reading, not a Lean spectrum theorem.
No certified coherent receiver supplies the per-flip amplitude, so the
amplitude stays an explicit hypothesis.

**One firing site: finite observation (Task 2).** `tools/bit_ring_rate_check.py`
computes, without data, the 43-tick flag count for one firing site and one
start site on n-rings. For firing site 0 the counts by `x0` are:
`n=3: [14,14,15]`; `n=4: [10,11,11,11]`; `n=5: [8,8,9,9,9]`;
`n=6: [7,7,7,7,7,8]`; `n=7: [6,6,6,6,6,6,7]`;
`n=8: [5,5,5,5,5,6,6,6]`. On the 43-ring every firing site and every `x0`
give exactly **1** (distinct set `{1}`). This is a finite observation, not a
closed-form theorem and not a mass/tier. The general-n closed form was not
proved.

**Record writes are receiver flags (Task G, Step 1).** On `RingReceiver.State n`,
one tick satisfies `record_step_identity`: record occupancy after the tick
equals record occupancy before plus the number of exchanging sites with
arrivals `(true,false)` minus the number with `(false,true)`. The receiver
flag count is the sum of those two counts (`flagCountInt_eq`). The one-tick
absolute bound is `record_step_abs_le`, and its T-tick iteration is
`record_net_le_flagSum`. The port stream shift is a permutation, so it does
not break the identity.

**The EP record bit is a different object (Task G, Step 2, outcome b).**
`WireSchedule.bitToll` and `HeavyFlipRecords.orbit_record_tolls` count the
two exact electric record comparisons (`ElectricHeavyRecord.phase_position`,
`phase_sector`, `orbitBitPrice`). The certified objects are the `labelRecord`
bits and their exact-flag prices. `RingReceiver` has a record-stream Boolean
port; no certified map identifies `labelRecord` with that port or with the
record occupancy used above. The objects needing identification are the
`WireSchedule`/`HeavyFlipRecords` record bit, `ElectricHeavyRecord`'s exact
comparison flag, and the `RingReceiver` record-port value/occupancy. This is
gap U. Step 3 was therefore not run.

**Achievable 43-tick sums (observation).** On the 3-ring, `patternTable` via
`localizedSum43_eq_pattern` gives exactly `{0, 14, 15, 21, 22, 43}` over all
request fields, both rules and all `x0`. The n=4 full 43-tick decide exceeded
600 seconds and was stopped; the n=4 zero/empty result
`localizedSumN_four_zero_iff_empty` is still certified. These are
registration counts, not masses or tiers.

**Label constraints (Step 3).** No certified EP or KAutomaton result states
that a packet with a given label needs at least k *receiver* registrations.
The available requirements are in other ledgers: `EventRequirements.massive_flag`,
`DiagonalReadout.state_flag`, `ElectricHeavyRecord.phase_position` /
`phase_sector`, `HeavyFlipRecords.orbit_record_tolls`, `WireSchedule.bitToll`,
`CoherentGate.unequal_needs_orthogonal`, and `GenerationWalls` concern record
bits, readout flags or endpoint distinctions. The missing link is a certified
map from a label's record/readout requirement to `RingReceiver.receiverFlag`.
No such link is created here.

No certified KAutomaton result forces the retained request field to be the
same at every site. `HomogeneousRouting.equivariant_is_translation` constrains
the routing permutation, not the retained requests; `LocalController.radius_one`
states local dependence. Homogeneous requests are therefore a named hypothesis
(`HomogeneousRequests`), not a derived result. Under that hypothesis, the four
uniform request values are enumerated. On the 3-ring, `uniform_falsefalse_sums`
gives 0 under AND and OR, `uniform_truetrue_sums` gives 43 under both, and the
mixed uniform values give 0 under AND and 43 under OR
(`uniform_truefalse_sums`, `uniform_falsetrue_sums`).

The localized embedding and occupancy check generalize to `Fin n`
(`localizedPortsN`, `localizedPortsN_occupancy`,
`localized_occupancy_preservedN`). For `n = 3,4,5,6`:
`empty_uniform_flags_zero` gives zero for every tick and any `T`;
`full_uniform_flag_count_three` … `_six` give exactly one flag per tick in the
43-tick window, and `full_uniform_sum43_three` … `_six` give 43. The register-
per-tick case has the form of a direction flip each tick (the Feynman
checkerboard reading of mass as a direction-flip rate); that reading is a
hypothesis for later, not a result here.

The hold/FIFO packet lifts are not derived booking rules. `hold_cell_fixed`
and `fifo_lift_differs` identify their bank actions, but neither determines a
receiver booking tick set.

The heavy record reference remains the certified two-element family
`{lepton, colour}`. The tier sets in `TierLedger` remain premises.

### Finite witness output

`Values.TransportCandidates` keeps only the uniform control field. Its
receiver column is zero by equal arrivals; it is not a one-excitation result.
The localized 43-tick sums are the `patternSum` table above, conditional on
the exchange pattern from the retained request field. The record Toll is a separate column. The heavy
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

## Protocol readout

Numerical, `tools/protocol_readout_scan.py`. On the derived wire (`PMAction.ReferenceClassHop`: reference wall `κ_R = (K, k, k)`; `PMAction.CarrierAdmittance`: other wall class-blind, `κ_O = (K, K, K)`; `K = 1`) the cycle resonance is `δ³ = −1` (`PMAction.OtherWallStationary`). At every cube root the bare wire has `m₁ = 0` and `m₂/m₃ = √3 k / √(2 + k²) ≈ √(3/2) k`: `0.0045` for `k = α/2`, `0.0089` for `k = α`, the same for every protocol. The data (`m_μ/m_τ = 0.0595`, `m_s/m_b ≈ 0.019–0.022`, `m_c/m_t ≈ 0.0036–0.0042`) then need a weight `s` on the heavy label (both walls) per protocol: `s_e : s_d : s_u ≈ 1 : 2.7–3.2 : 12–13.5` for `α/2` (`1 : 2.6–3.1 : 9.6–10.6` for `α`), ordered by charge; the heavy label's mass scales as `s²`. The lazy flip law squares the bare ratio (`2·10⁻⁵`), far below every protocol, so the data favour the coherent event. CKM on the derived wire (weights as fitted): same root `|V_us| ≈ 0.0001`, `|V_cb| ≈ 0.009`, `|V_ub| ≈ 0.008`; different roots `|V_us| = √3/2 ≈ 0.866`, `|V_cb| ≈ 0.010`, `|V_ub| ≈ 0.011` (data `0.225`, `0.041`, `0.0037`): the bare wire's rotation is not the CKM. Mixing tests on the derived wire (`tools/mixing_candidates_check.py`, masses held at data): `|V_us| = 0.225` is reached by a relative flip phase, a light-class asymmetry, or an other-wall cycle phase or asymmetry, so it does not discriminate; `|V_cb|` stays at `0.002–0.010` under every deformation tried (those, the weight on one or both walls, a joint fit, `k/K` from `α/4` to `10α`), with `|V_cb| ≈ |V_ub|`. So the wire's mass matrices cannot give `|V_cb|`; PMFlavor's transfer readout does (`PMFlavor.ReferenceRouting`). Charge-weight test: one `a` in `s ∝ e^{a Y_R}` gives down and up `0.82` and `0.77` (PDG mixed scales), `0.74` and `0.75` (`m_b`, `m_t` at their own scale), 2–11% apart across quark-mass choices (`k = α/2`; `7–18%` at `k = α`). Lightest masses: a real offset `δ = −1 + ε` off the resonance reproduces each `m₁/m₂` with `ε ≈ 0.038 (e), 0.14 (d), 0.0024 (u)`, keeping `m₂/m₃` within 2–7%; with those offsets the same-root CKM is `|V_us| ≈ 0.063`, `|V_cb| ≈ 0.007`, `|V_ub| ≈ 0.0065`.

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

The [generation comparison](GENERATIONS.md#the-charged-lift) counts the
same selector and crossing support for every charged label.
`det_flip_at_resonance` gives the same linear response to the supplied
offset in each selected sector. Its order in `1/Δ` depends on the firing
law for that offset.

The [phase and handoff calculation](GENERATIONS.md#phase-handoff-and-toll)
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
| `HeavyFlipNativeBoundary.no_closed_cleaning`, `tick_event_iff`, `idle_and_excursion_counts`, `cycle_closes`; `GappedGluedCrossing.equalClass_iff` | The untagged probe aliases addresses and closed universal cleaning is impossible. Both idle and two-toggle masks close. The gapped crossing shifts generation. | Address and ready record needed for the clocked endpoint. Separate Schur insertions still need their own firing law. |

[Persistence selection](SCHEDULE.md) enumerates a bounded serial family.
[Packet reference cost](SCHEDULE.md#which-population-is-charged)
derives uniform weights under the full-packet sampling premise and
checks the vacancy contribution. The full-packet bit gap is `−1/2`
per sampled input when the vacancy is probed. The smaller support
and the idle-vacancy rule have separate thresholds. The
[lifecycle comparison](SCHEDULE.md#record-reference-remains-undetermined)
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

## Tier ledger and the wire

The [generation comparison](GENERATIONS.md) connects the three glue addresses
to one direct and two node-mediated routes. It distinguishes address from
mass rank and compares the shared heavy-to-middle power with the declared
tiers. The bare wire's lightest mode is zero at resonance.

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
modes alone. Experimental comparisons belong to the e8p report.
The physical schedule and readout remain open. The native current on these states is
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
