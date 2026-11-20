# PMElementaryParticles — historical working ledger

This file preserves the task-numbered working history moved out of
[OVERVIEW](OVERVIEW.md) and [REVIEW-AND-NEXT](REVIEW-AND-NEXT.md). Content is
kept unchanged except for section headings.

## Historical OVERVIEW detail

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

The colour composite is not a single-site vacuum. The smallest certified
object carrying it is the three colour-axis vectors `+2e_1,+2e_2,+2e_3`,
acted on by `PacketGaugeActions.permuteColour` and `record_colour`; the layout
references `SharedReference`/`ColourReference` supply no such composite state.
The nested-paper rules—Capacity Partitioning, Reversible Encoding and
Impedance Matching (`PM-3-Nested/paper/2_nested_persistence.tex`)—do not define
a multi-protocol composite state on the machine. Colour-referenced protocols
therefore cannot be tested for all six pillars inside a composite without that
missing definition.

No certified E8 line carries the abstract `Fin 3` bit ring. `AxisHop` proves an
axis step is two root events; `OpenHandoff` routes along a primitive root
direction, not the vacuum axis vector `2e_0`. The map from the bit ring to a
line through `+2e_0` is missing, so the lattice period/rate cannot replace the
3-ring registration counts. Those counts remain 3-ring artifacts.

Per-generation tier comparison is observation only. The attached model has no
per-generation cost; `crossing_word_glued` and the clock periods give the
certified extra work, but not a protocol-class price. The TierLedger orders
`1/Δ` and `1/Δ²` are listed only for later comparison, not derived here.

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



## Historical isolated-excitation detail

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



## Historical REVIEW detail

# PMElementaryParticles — open work

## Current open list

1. Certify the bit-ring-to-lattice line through the vacuum vector, or name the
   missing map.
2. Settle shared, sector-local or composite background; colour needs a
   three-part composite, lepton is a single vector.
3. Define the multi-protocol composition state from the nested-paper rules and
   rerun alone/together closure.
4. Run triality on the attached valid set and derive per-generation costs; the
   TierLedger orders remain observation only.
5. Finish the full-ring Lean spectrum; the mass reading remains a hypothesis.
6. Radiative stage 2 remains not started.

The detailed status sections below are the historical working ledger.


**Rebuild plan.** EP is being rebuilt from persistence on the certified
KAutomaton machine. Order: (1) machine EP uses; (2) finite `Protocol`;
(3) six pillar predicates from `PersistenceMechanics.Requirements`;
(4) complete finite enumeration; (5) legacy audit. Current status:
`Protocol`, its complete finite family, and the weakest pillar predicates are
defined. The filter is evaluated; a direct `decide` over all protocols exceeded
600 seconds, so survivor counts are observations. Alone/together composition
stops at the missing multi-protocol state. Legacy results are retained and
audited, not deleted.


[OVERVIEW](OVERVIEW.md) records the checked operations. **[Premise]**
marks a physical identification or rule still to be derived.
**[Certificate]** marks a calculation awaiting formal verification.

## Rebuild Tasks 2–5 status

`PersistenceMechanics.Requirements` defines the three requirements, six pillar
names, requirement/sign maps and abstract `PMRequirements`; it does not define
six physical predicates on a machine state. Task 2 stops at that missing
definition. Task 3 enumerates the complete finite `Protocol.allProtocols`
(24,576 protocols) but applies no six-pillar filter. Task 4 finds no certified
loop-closure predicate and no identification of bit-ring position with the
Delta clock phase. Task 5 cannot decide alone/together closure without the
missing predicates; no grouping or confinement is assumed.

**Legacy single-reference assumptions after P3.** The least-Toll reference is
per label: up→lepton, down→colour, electron→lepton, neutrino→colour.
`down_geometric_mean` still holds numerically because the selected Tolls are
all 1, but its colour-row premise is no longer universal. The record Toll rows
`(2,1,0,1)`/`(1,2,1,0)` remain valid per reference; per-label selection mixes
entries from both. The legacy heavy writer's single reference is contradicted
as universal and remains conditional per label.

**Legacy audit after the filter.** Map derives reference exclusions per label
(Hamming ≥ 1: up needs lepton, neutrino needs colour; Hamming = 2: only the
complementary record). Toll excludes empty firing; Margin excludes full firing
under the per-ring variant. Tier sets, generation addresses, quark/lepton
formulas and heavy-label weights remain premises; record Tolls remain derived
at the flag level and conditional on the physical record-port identification.

## Pillar filter status (Tasks 1–5, P3 correction)

`PillarPredicates` defines the weakest paper predicates. Margin's corrected
form is `marginUtilization`: every registering ring has period count `< 43`,
directly the Fragility/utilization failure mode. `marginPerRing` and
`marginTotal` remain named proxies only.

`SurvivorClasses` quotients the raw label to `labelRecord`
(`satisfies_labelRecord_invariant`, `survives_iff_reduced`). With corrected
Margin, reduced survivor counts are `SurvivorsU false = 1650`,
`SurvivorsU true = 1110` (`survivorsU_cards`). The robust core is the
intersection of both Toll variants; its direct reduced decide exceeded 600
seconds, so the intersection count, table and minima below are evaluation
observations. The corrected class table:

| record | reference | reduced survivors | period counts |
| --- | --- | ---: | --- |
| up | lepton | 240 | 14,15,21,22 |
| up | colour | 0 | — |
| down | colour | 240 | 14,15,21,22 |
| down | lepton | 75 | 28,29,30,35,36,37,42,43,44 |
| electron | colour | 75 | 28,29,30,35,36,37,42,43,44 |
| electron | lepton | 240 | 14,15,21,22 |
| neutrino | colour | 240 | 14,15,21,22 |
| neutrino | lepton | 0 | — |

The corrected Margin removes every single-ring 43 and the two-ring 86; a total
of 43 remains only as a two-ring sum. Least Toll gives the same minimum 14 for
every label; the least-Toll reference is up→lepton, down→colour,
electron→lepton, neutrino→colour, unique for up/neutrino and for the
both-valid rows because the minima differ.

**Task P4: shared vs per-label reference.** Step 0 is proved:
`satisfiesUtil_perRing_imp_total`, `robustCoreU_eq`, `robustCoreU_card = 1110`.
Step 1 outcome is **(c) not certified**: the library certifies two D4 sectors
and a stationary connected background, but no map from the abstract `Fin 3`
bit-ring background to an E8 lattice/D4 sector and no assignment of record
classes to sectors. The P3 per-label references are therefore conditional.

Conditional shared tables: colour valid for down/electron/neutrino with minima
`14,28,14` (up fails Map); lepton valid for up/down/electron with minima
`14,28,14` (neutrino fails Map). No shared vacuum is valid for all four record
classes. Under shared colour the row is `(2,1,0,1)` and down/up identity is
nontrivial; under shared lepton it is `(1,2,1,0)` and the down identity fails
nontrivially. P3 per-label refs make all selected Tolls 1, so the identity is
only an equal-Toll special case. The heavy writer's single reference is
consistent only with a shared vacuum, which is not certified.

**Task P5: record coordinates and E8 placement.** `RecordCoordinates` proves
`labelIndex = 2*axis + sign` and `labelRecord = (axis=0, sign=1)`. This is a
finite-code coordinate statement only. No theorem identifies `labelIndex` with
the minimal vectors of a specific D₄ glue class, despite
`Channels.minimal_class_card` and `Channels.nu_eq`; the sector/class bijection
is missing. All 16 channels are therefore not certified to lie in one D4
sector; per-sector backgrounds are not excluded.

The reference records are colour `(axis≠0,sign0)` and lepton
`(axis0,sign0)`. `SharedReference` and `ColourReference` are layout/payload
objects; neither is proved equal to either `refRecord`. Outcome: references are
not identifiable with a certified E8 object.

No certified line in E8 carries the abstract bit ring. The links in `AxisHop`,
`NativePacketLinks`, `OpenHandoff` and `GenerationWalls` are qualified moves,
but the bit-ring-to-lattice background map is missing.

**E8 attachment.** `ChannelVectors.channelCoord` gives the full 16-channel
map: active-false `vectorCoord` is `sign·2e_axis` in the vector class;
active-true `spinorCoord` is its certified triality image in the adjacent
class. `channelCoord_norm4`, `channelCoord_glueClass`,
`channelCoord_injective`, and `channelCoord_image_card = 16` prove the
injection onto minimal vectors of two classes. The orientation is fixed by the
certified `c ↦ c+1` triality. The three attachments are its triality powers;
the attachment index is the generation/glue address.

Under the vector attachment, lepton reference is `+2e_0`; colour reference is
the set `{+2e_1,+2e_2,+2e_3}`. `NativeReferenceBackground.stationary_iff`
permits a single-site lepton background but not the full colour set; the
colour option needs a three-part composite of colour-axis vectors.
`SharedReference`/`ColourReference` are still layout objects and are not proved
equal to these. In the lepton vacuum neutrino fails Map; in the colour
composite up fails Map.

The colour reference cannot be one site value; the smallest candidate carrier
is the three colour-axis vectors, using `PacketGaugeActions.permuteColour` and
`record_colour`. `SharedReference`/`ColourReference` do not define that
composite. The nested composition rules (Capacity Partitioning, Reversible
Encoding, Impedance Matching) do not define a multi-protocol machine state, so
colour-referenced all-pillar closure inside a composite remains conditional.

No certified E8 line carries the abstract bit ring: `AxisHop` has axis steps as
two root events, and `OpenHandoff` follows a primitive root direction, not the
`2e_0` vacuum axis. The lattice line/period map is missing. The 3-ring
registration counts remain artifacts. Triality checks and per-generation costs
remain conditional; `crossing_word_glued` and clock periods give extra work but
no protocol-class cost. Tier-ledger orders remain observation only.

The nested-paper composition rules (Capacity Partitioning, Reversible Encoding,
Impedance Matching) do not define a multi-protocol state on the machine, so
alone/together closure stops at that missing definition. No grouping is assumed.

## Isolated-excitation input and trace

A mass is the property of one isolated excitation on the vacuum. The sector
is fixed in `IsolatedExcitation`: a stationary E8 reference plus one packet
carrying a single 16-slot label. `occupiedInput_admitted` proves the valid
two-bank occupancy and `occupiedInput_supply`/`occupiedInput_acceptance` are
the existing supply and acceptance results. This is the definition of the
quantity, not a choice of O. The vacuum is a certified family
(`vacuum_nonunique`).

`IsolatedReceiverTrace` now separates the uniform control field from the
localized one. `uniformPorts` has six true bits when the packet is active and
fails the occupancy check (`uniformPorts_occupancy`); its zero flags under AND
and OR (`uniform_flag_zero_AND`, `uniform_flag_zero_OR`, `uniform_AND_OR_tie`)
are equal-arrival artifacts, not isolated-excitation results.
`localizedPorts x0 packet` has one live packet at `x0`, record vacuum there,
and vacuum elsewhere; its occupancy is one when active and zero otherwise
(`localizedPorts_occupancy`) and is preserved by `tick` under both rules
(`localized_occupancy_preserved`). Requests are retained
(`localized_requests_retained`) and the localized port field has period 12
(`portStep_period_twelve`), so the 43-tick sum is three periods plus seven
ticks (`localizedSum43_eq`). The sum depends only on the exchange pattern
(`localizedSum43_eq_pattern`, `patternSum`). AND and OR differ exactly when
their pattern-table entries differ (`localized_and_or_differ_iff`,
`sumsDiffer`). Simultaneous rotation of packet site and requests leaves the
sum unchanged (`localizedSum43_rotate`); for fixed requests it can depend on
`x0` (`localizedSum43_x0_depends`). An inactive packet gives zero
(`localizedSum43_inactive_zero`). The receiver registrations per period and
the record bit visits remain separate columns with no certified common ledger.
The hold/FIFO packet lifts move the bank but do not determine a booking tick
set, so that stop remains.

### Homogeneous requests and ring size

**Unconstrained least Toll (Task F, Steps 1–2).** On the 3-ring,
`localizedSum43_eq_zero_iff_empty` gives receiver sum zero iff the exchange
pattern is empty, and `localizedSum43_nonempty_ge_fourteen` gives every other
pattern at least 14. PM least Toll therefore selects the empty firing pattern:
AND selects request fields with no `(true,true)` site
(`and_zero_iff_no_true_true`); OR selects request fields with every site
`(false,false)` (`or_zero_iff_all_false`). An unconstrained isolated packet
never registers. On the 4-ring the same result is
`localizedSumN_four_zero_iff_empty`; the n=5 decision run did not finish within
ten minutes and was stopped at n=4.

**Label constraints (Task F, Step 3).** No certified result says a labelled
packet needs at least k *receiver* registrations. The existing requirements
are record/readout flags (`EventRequirements.massive_flag`,
`DiagonalReadout.state_flag`, `ElectricHeavyRecord.phase_position` /
`phase_sector`, `HeavyFlipRecords.orbit_record_tolls`,
`WireSchedule.bitToll`, `CoherentGate.unequal_needs_orthogonal`,
`GenerationWalls`). The missing link is a certified map from those
record/readout requirements to `RingReceiver.receiverFlag`; none is invented
here.

**Task I reference-background bit rings (hypothesis, not certified).** The
candidate vacuum is the reference record on both streams everywhere; a packet
replaces the live bits at one site. Each record bit has its own ring and
requests. The references are colour `(false,false)` (up record) and lepton
`(true,false)` (neutrino record). `bitToll_eq_hamming` and `colour_hamming`
reproduce the EP rows. Complement symmetry is `tick_complement` and
`receiverFlag_complement`. `bitRingEmbed` is the bit-ring state;
`bitRingEmbed_equal_zero`, `bitRingEmbed_background_fixed`,
`bitRingEmbed_false_true`/`bitRingEmbed_true_false` and `bitRingSum43_eq` give
the per-bit 43-tick result. The native stationarity bridge is
`bitRingConfig_stationary` with `bitRingConfig_streams` and
`bitRingPortBackground_fixed`. `bitRingTotal43_eq` gives the total over the two
rings; `bitRingTotal43_shared` gives
`bitToll ref c * patternSum (firingPattern either r) x0`. Unconstrained least
Toll is zero for every label (`bitRingTotal43_empty_zero`); a zero-Hamming
label is zero for every request field (`bitRingTotal43_hamming_zero`). The
Task H encounter scaffolding was removed. This remains a hypothesis, not a
certified identification.

**Task 3 reference choice: (c), free.** `ColourReference.colour_reference_in_payload`
locates a colour reference in the payload but does not select a writer record;
`SharedReference` supplies a reserved layout cell. Neither identifies the
bit-ring reference with colour-up `(false,false)` or lepton-neutrino
`(true,false)`. `vacuum_nonunique` gives rest modes, not record bits. The free
choice enters in `refRecord` / `bitRingEmbed refBit`.

**Task 4 firing requirement: (b), other ledger only.** No certified result
requires an excited bit to register again. `CoherentRefresh.minimum_once`,
`RefreshSchedule.minimal_is_ledger`, `ReferenceMaintenance`,
`RecordSupply.clean_supply`, `CoherentRecordRestoration.twice_undoes` and the
conservation requirements are refresh/maintenance/occupation statements. The
missing link to `receiverFlag` is gap U; no requirement was created.

**Task 5 checkerboard test (hypothesis amplitude).**
`tools/bit_ring_checkerboard.py` gives a gapless empty-firing ring and a gapped
full-firing ring with gap `theta` and a small-`k` Dirac-like fit
`E^2 ≈ sin^2 k + (theta/2)^2`. Script-level pass only; no Lean spectrum
theorem and no certified coherent per-flip amplitude. The amplitude remains a
named hypothesis.

**One firing site: finite observation (Task 2).** `tools/bit_ring_rate_check.py`
gives 43-tick counts for firing site 0 by `x0`: `n=3 [14,14,15]`,
`n=4 [10,11,11,11]`, `n=5 [8,8,9,9,9]`, `n=6 [7,7,7,7,7,8]`,
`n=7 [6,6,6,6,6,6,7]`, `n=8 [5,5,5,5,5,6,6,6]`. On the 43-ring every
firing site and `x0` give exactly 1. No general-n closed form was proved;
these are observations, not masses/tiers.

**Record writes are receiver flags (Task G, Step 1).** `record_step_identity`
on `RingReceiver.State n` equates the one-tick change in record occupancy with
exchanging `(true,false)` arrivals minus exchanging `(false,true)` arrivals;
`flagCountInt_eq` identifies the receiver flag count with the sum of those
counts. `record_step_abs_le` and `record_net_le_flagSum` give the one-tick and
T-tick absolute bounds.

**Task G, Step 2 outcome: (b).** `WireSchedule.bitToll` and
`HeavyFlipRecords.orbit_record_tolls` count `labelRecord` exact flags
(`ElectricHeavyRecord.phase_position`/`phase_sector`, `orbitBitPrice`). No
certified map identifies that record bit with a `RingReceiver` record-stream
port or with record occupancy. The gap-U objects are the
`WireSchedule`/`HeavyFlipRecords` record bit, the `ElectricHeavyRecord` exact
comparison flag, and the `RingReceiver` record-port value. Step 3 was not run.

**Achievable 43-tick sums (observation).** On the 3-ring the distinct sums
are `{0,14,15,21,22,43}` (`patternTable`, `localizedSum43_eq_pattern`). The
n=4 full 43-tick decide exceeded 600 seconds and was stopped; the n=4
zero/empty theorem `localizedSumN_four_zero_iff_empty` remains. These are
registration counts, not masses or tiers.

**Finding (Task E, Step 1).** Requests are independent initial data; no
certified relation to the reference background exists. `ClockedRootTrials`
takes the controller background `initial : Finset M` and the request
projection `requestOf : M → Bool × Bool` as separate supplied inputs
(`historyCount`), and its module states that the background and its request
projection are separate inputs. `LocalController` keeps requests in the
supplied register state; `RingReceiver` retains them; the native background
stores reference values, not requests. No map from the background
configuration to the request field is certified.

Consequently no certified result forces the retained request field to be
site-independent. `HomogeneousRouting.equivariant_is_translation` constrains
the routing permutation; `LocalController.radius_one` is local dependence.
Homogeneous requests are a named hypothesis (`HomogeneousRequests`), not a
derived result. Steps 2–3 of Task E were not run.

Conditional on that hypothesis, the four uniform requests are enumerated on
the 3-ring: `(false,false)` gives 0 under AND and OR; `(true,true)` gives 43
under both; a mixed request gives 0 under AND and 43 under OR
(`uniform_falsefalse_sums`, `uniform_truetrue_sums`,
`uniform_truefalse_sums`, `uniform_falsetrue_sums`).

The localized embedding and occupancy check are generalized to `Fin n`.
For `n = 3,4,5,6`, an empty uniform firing pattern gives zero at every tick
for any `T` (`empty_uniform_flags_zero`); a full uniform firing pattern gives
exactly one flag per tick in the 43-tick window
(`full_uniform_flag_count_three` … `_six`) and sum 43
(`full_uniform_sum43_three` … `_six`).

The register-per-tick case has the form of a direction flip each tick. The
Feynman-checkerboard reading of mass as the direction-flip rate is a
hypothesis for later, not a result of this library.

## Certified coin and spectrum (Task L)

The certified converter has pass/flip amplitudes `(1 ± e^{ix})/2`
(`converter_plus`, `converter_minus`), i.e. `cos(x/2)`/`sin(x/2)` up to a
common phase. `encounter_unitary` certifies the coherent encounter;
`exact_bit_flip` gives the `x = π` full flip. `tools/bit_ring_checkerboard.py`
verifies the full-firing block dispersion `cos E(k) = cos(x/2) cos k` to
machine precision, gap `x` at `k=0`, and a gapless empty-firing ring. The Lean
full-ring block proof was not completed; the exact-bit and k=0 cases are
certified. The mass reading remains a hypothesis.

## Phase-to-record converter (Task K)

The certified `CoherentComparisonRepair.compare (InterferenceReadout.phase x)`
is the converter (`PhaseToRecord.converter_unitary`). On `phaseInput`, its minus
output has probability `DiagonalReadout.flag x` (`minus_probability`), and the
expected receiver flag is `flag x` (`expected_receiver_flag`). The two converted
branch records are orthogonal (`converted_records_orthogonal`) and meet
`CoherentGate.unequal_needs_orthogonal` (`converted_branch_records_unequal`).
`bitToll_eq_expected_conversion` recovers the EP row. The factor of two is only
the phase (`nsq/4`) versus orthogonal (`nsq/2`) encoding. Gap U's flag
identification closes for all phases; no new unitary was defined.

## Common comparator (Task J)

KAutomaton W and G are certified and removed from its open ranking:
`receiver_flag_eq` and `localized_period_registrations_eq`; `RingReceiver.tick`
and `receiver_flag_eq`.

The receiver and electric flags share a `CommonResponse` parent only up to
normalization. `CommonResponse.stateFlag` is `nsq(φ − Uφ)/4`;
`DiagonalReadout.flag` is `(1 − cos x)/2`; `DiagonalReadout.state_flag` is the
weighted diagonal average. `CommonComparator.exchangeFlag_eq_two_linkFlag`
makes the receiver comparison twice the identity `linkFlag`, and
`CommonComparator.flag_eq_stateFlag` makes the electric flag the unit-phase
`stateFlag`. EP's exact record bits are `DiagonalReadout.flag` values
(`ElectricHeavyRecord`, `bitToll_eq_hamming`). The factor-two normalization
remains; this is not a certified identification and gap U stays open.

## EP protocol ownership

`IsolatedReceiverTrace` and `RecordPortIdentification` are EP protocol work that
use the KAutomaton machine. EP owns the protocol inputs: retained request field
and firing pattern G, excitation occupancy and reference-record choice O, the
label record/reference/theta part of U, which label record W reads, the label
Toll/paid-event part of K, and the history/prior family H. The certified label
dependence is `bitToll_eq_hamming`, `refRecord`, `bitRingTotal43_eq` and
`firingPattern`. KAutomaton retains the common comparator, receiver-flag
computation, tariff unit, links, boundary, clock and job mechanics.

## Protocol readout blockers

EP inherits a [conditional KAutomaton interface](../PMKAutomaton/COMPONENTS.md#kautomaton-closeout).
Its open inputs follow the [KAutomaton ranking](../PMKAutomaton/COMPONENTS.md#remaining-free-inputs-by-reach).
The supplied source, operation, read and cost must refer to the same trace.

| Ranked inputs | EP decision |
| --- | --- |
| G, T | Phase, requests and probe are named open controller fields in `ReceiverFields`. Requests are retained and enumerated by their exchange pattern. The localized 43-tick sum is `patternSum (firingPattern either r) x0`; AND and OR differ exactly when those table entries differ (`localized_and_or_differ_iff`). The hold/FIFO lifts do not determine booking ticks. |
| O, U, W | The isolated occupancy is vacuum plus one packet and is certified. `localizedPorts` places the live packet at one site and leaves the record stream at vacuum; the uniform control field is rejected by the occupancy check. The localized receiver flag is computed by `receiver_flag_eq`; the record Toll remains a separate column. General routing and writer attachment remain open. |
| K, B, D | The localized receiver sum is the `patternSum` table; the record bit-visit column is separate with no common ledger. General tariffs remain open. |
| J, Q, H, L | The localized embedding has one state family; the request field is an enumerated input, not a selected history. J, Q and L remain open. |

- **Heavy-label weight. [Certificate]** The isolated receiver trace gives
  zero registrations under both rules. The certified record columns colour
  `(2,1,0,1)` and lepton `(1,2,1,0)` remain separate and no isolated trace
  selects a physical record reference.
- **Lightest masses. [Premise]** Supply the admitted static selector
  and the charged offset on that leg. The
  [generation ledger](GENERATIONS.md#the-charged-lift) gives the exact
  conditional linear response. Its phase and route certificates
  do not set an inverse-period order. Derive the same calibrated
  generator before comparing to the first-row PMFlavor readout.
- **Species and neutral modes. [Premise]** The species assignments in
  `QuarkMasses`, `LeptonMasses` and `TierLedger` are a declared ledger.
  The localized trace has no address-to-tier bit, so it cannot replace the
  tier sets. For neutrinos, admit the
  static neutral partner and the coherent branch mixer in
  `BranchGateBoundary`. The paired Schur block requires unequal magnitudes
  of the reverse-cycle weights for a split from diagonal flips. See
  [the static vacancy](OVERVIEW.md#static-vacancy-and-neutral-light-modes)
  and [the gapped crossing](OVERVIEW.md#equal-class-gapped-crossing).

## Other open work

- **Radiative factor. [Certificate]** The substrate's own order-`α`
  correction is derived numerically from the diagrams
  (`tools/muon_radiative_derivation.py`): the conserved wall vertex
  (`PMAction.SpinorVertex`, `Z₁ = Z₂` on the substrate), continuum photon
  modes, the virtual vertex and both self-energies, and real emission at
  fixed neutrino-pair invariant, with explicit ultraviolet, infrared and
  collinear regulators. The total is independent of each regulator and
  reproduces the inclusive kernel pointwise (`z = 0.1 … 0.9`, to `10⁻⁴`
  relative at `m_e = 3·10⁻⁴`), so its integral is `π² − 25/4`
  (`tools/muon_radiative_certificate.py`). Radiative stage 2 has not been
  started: it must assemble the vertex, self-energy and real-emission diagrams
  and show the regulator logs cancel. Until stage 3, `MuonLifetimeCorrected`
  keeps the factor as a certified input, and the higher-order terms
  (`MuonQEDLoops`) stay supplied.

## Rebuild closeout and next priority

**Certified machine.** KAutomaton is closed on its conditional interface;
receiver flags, guard table, record bookkeeping, bit-ring sums, native
stationarity bridge, phase-to-record converter, and the coherent coin are
certified. KAutomaton's remaining named machine inputs are T, L, B, D, J, Q and
the tariff unit.

**EP protocol layer.** `Protocol.Protocol` is finite: 16 labels × 2 references
× firing patterns × certified phases `{0,π}` × packet site; the full family is
`Protocol.allProtocols` and `allProtocols_complete`. `PillarPredicates` defines
the weakest paper predicates. The corrected Margin is `marginUtilization`
(every registering ring has period count `< 43`); `marginPerRing` and
`marginTotal` remain named proxies. `SurvivorClasses` quotients the raw label to
`labelRecord`; `survivorsU_cards` proves `SurvivorsU false = 1650` and
`SurvivorsU true = 1110`. The robust core is proved without a decide:
`satisfiesUtil_perRing_imp_total`, `robustCoreU_eq` and
`robustCoreU_card = 1110`. The corrected class table has one-differing-bit rows
with counts `{14,15,21,22}` and two-differing-bit rows with
`{28,29,30,35,36,37,42,43,44}`. Single-ring 43 and two-ring 86 are gone; 43
remains only as a two-ring sum. Per-label least Toll gives the same minimum 14
for every label: up→lepton, down→colour, electron→lepton, neutrino→colour.
Those per-label references are conditional because the shared-versus-sector
background question is (c) not certified (Task P4).

**What remains.** The full channel→minimal-vector map is certified
(`ChannelVectors.channelCoord`), but no certified bit-ring-to-lattice line map
exists, so shared/per-sector backgrounds and per-sector tables remain
conditional. The colour reference cannot be a single-site vacuum; it needs a
three-part colour composite, and the multi-protocol composition rules are not
defined on the machine. In the lepton vacuum neutrino fails Map; in a colour
composite up fails Map. The firing pattern is not selected and the full-ring
Lean spectrum is not proved. Legacy tier sets, generation addresses,
quark/lepton formulas and heavy-label weights remain premises; record Tolls are
derived at the flag level. `down_geometric_mean` holds nontrivially under
neither single shared vacuum; under the conditional per-label Tolls all
selected Tolls are 1, so it holds only as an equal-Toll case.

**Next EP priority.** Certify the bit-ring-to-lattice line (or state its
missing map), then settle shared versus sector/composite backgrounds. After
that, define the multi-protocol composition state from the nested-paper rules,
select the firing pattern, and finish the full-ring spectrum. The mass reading
remains a hypothesis; radiative stage 2 is separate and still not started.
