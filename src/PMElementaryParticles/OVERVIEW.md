# PMElementaryParticles — checked results

EP studies the elementary programs above the E8 node machine. It imports PMSubstrate,
PMAction, PMConstants and PMKAutomaton. See [README](README.md), [TODO](TODO.md) and
[SCOPE](../../SCOPE.md#named-premises). This step proposes a nested architecture;
it derives no new species values, workloads, level budgets or generation-to-tier map.

## Fermions as nested systems

A proposed tier n has n nesting steps above the level-0 ring: levels 0 through n.
Every level must realize all six pillars. `NestedFermion` gives the role map and its
sources. `LedgerLevels` supplies exact algebra for the declared ledgers, not a derivation
of those roles from their coefficients. The downstream `PMAtoms.SystemTower` illustrates
the additive form; EP does not import it.

| Rule | Canonical Lean source | Required application data | Does not imply |
| --- | --- | --- | --- |
| 1: Capacity Partitioning | `PersistenceMechanics.CapacityPartitioning` | Work per specified deadline, worker capacities, overhead, complete service. | A unique allocation, nesting depth or a feasible schedule from an aggregate bound. |
| 2: Reversible Encoding | `PersistenceMechanics.ReversibleEncoding` | States, coarse descriptions, retained metadata, injectivity or a decoder. | A storage price, update frequency or maintenance workload from alphabet cardinality. |
| 3: Impedance Matching | `PersistenceMechanics.ImpedanceMatching` | The transfer law, incident load, source/load impedances and reserve. | Zero mismatch or a numerical tolerance without a reserve law. |

| EP adapter | Actual objects | Per-level? | Status for this step |
| --- | --- | --- | --- |
| `CapacityLedger` | Tasks = protocols sharing one ring. Demands = registrations/period. Overhead = supplied comparisons. Capacity = 43, less a supplied reserve. | No level index, child tasks or workload generator. | Reusable conditional budget adapter. A proved reserve is needed to use 42. |
| `RecordEncoding` | States = Channels. Coarse data = labelRecord. Metadata = channelCode. Fibres have six or two states. | No generation coordinate or nested codec. | Reusable Rule-2 channel adapter; its colour-reference construction does not define a generation level. |
| `ImpedanceLedger` | Encounters = supplied phases xs. Loads = expected pass/flag weights. Source/load = 1 minus/plus abs(sin(x/2)); reserve is supplied. | No levels, derived phases or per-level reserves. | Reusable interface algebra; legacy as a claim of an already derived level model. Expected reflected load is not a 42-slot service budget. |

## Per-level pillar roles

All rows above level 0 are architectural obligations. No operation, workload or cost is
claimed proved merely by giving it a role. Sources are Paper III Rules 1–3,
`PersistenceMechanics.Requirements.Pillar` and `PMSubstrate.Pillars`.

| Level | Capacity | Map | Protocol | Governor | Toll | Margin |
| --- | --- | --- | --- | --- | --- | --- |
| 0: ring | Registrations fit the period (`ProgramWitness.Capacity`). | Channel/reference distinction (`MapRecord`, `MapClass`); history merges generation. | Reversible ring tick (`tick_bijective`). | A non-firing site (`Governor`). | Quiet-equal-ring witness: one reversal, unit cost (`quiet_program_cost`). | At most 42 on a differing bit ring (`one_ring_margin_ceiling`). |
| 1: maintain level 0 | Service actual child reference, metadata and coordination work (Rule 1); work open. | Retain a reference for lost distinctions, including generation (Rule 2), and supply correction (`map_maintains`). | Reversible cross-level encoding and coordinated service (Rules 1–2); schedule open. | Restrict allowed child operations and contention (`Pillar.governor`); update open. | Count executed child-interface work; encounter and tariff open. | Positive robustness (`margin_iff`), service reserve and reflected-load reserve (Rule 3); units/implementation open. |
| 2: maintain level 1 | Service level-1 control and child interfaces (Rule 1); tasks open. | Derive the level-1 coarse description, retained metadata (Rule 2) and correction toward its reference. | Coordinate level-1 subsystems and preserve records; update and timing open. | Restrict admitted level-1 compositions; topology open. | Account for interface work without counting shared jobs twice. | Prove robustness (`margin_iff`), loop reserves and mismatch budgets. |
| 3: maintain level 2 | Service level-2 maintenance (Rule 1); no volume workload assumed. | Supply the level-2 reference/metadata (Rule 2) and correction toward it. | Reversible level-2 composition and a causal schedule. | Restrict the admitted level-2 architecture. | Price actual boundary work, not a guessed Delta power. | Prove robustness, loop reserve and interface budget for that implementation. |

| Structural result | Lean entry point | Limit |
| --- | --- | --- |
| Base histories coincide across generations for a fixed channel. Adding generation as metadata is injective. | `NestedFermion.base_history_merges_generations`, `generation_metadata_reversible` | This is a coarse-description instance, not a physical encoder. |
| Sufficient generation metadata has at least three states. | `generation_metadata_cardinality` | Three states is not three reversals or a service rate. |
| Differing bit rings have at most 42 registrations in the base period. | `one_ring_margin_ceiling` | A higher-level loop needs an identified implementation, differing condition and service interval. |
| Work plus overhead above 42 requires at least two such loops in any feasible realization. | `overload_needs_multiple_loops` | Fixed work/deadline and complete service are hypotheses. Calling extra capacity a new level needs the nested architecture. |

## Muon

`Muon.conditional_cost` gives n + rho under premise B ([SCOPE](../../SCOPE.md#named-premises)).
The base event kind is known; the held-child bank, parent period, sigma multiplicity,
anchor, phase price and feedback law remain open. See the six roles in its docstring.

## Declared ledger levels

These are [Premise] ledger identities. `increment A B` telescopes whole counts,
signed charges and residuals; `cost_tower` recovers the old scalar costs.
No physical division into level budgets or disjoint resource ownership is derived.

| Species | Declared level tower | Exact theorem | Remaining structure |
| --- | --- | --- | --- |
| Unit/electron entry | [unit] | `declared_electron_tower`, `declared_lepton_costs` | Physical point/species identification. |
| Muon | [unit, increment(unit, muon)] | `declared_muon_tower` | Level-0 maintenance workload and the level-1 operations. |
| Tau | [unit, increment(unit, muon), increment(muon, tau)] | `declared_tau_tower` | The increments cancel old residuals; no parent subsystem is derived. |
| Down | [down] | `declared_down_tower` | Physical point role and overhead. |
| Strange | [down, increment(down, strange)] | `declared_strange_tower` | Level-1 work and operations. |
| Bottom | [down, increment(down, strange), increment(strange, bottom)] | `declared_bottom_tower` | Level-2 work and operations. |
| Up | [up] | `declared_up_tower` | Physical point role and overhead. |
| Charm | [up, increment(up, X), increment(X, charm)] | `declared_charm_tower` | X is the unknown cumulative footprint through level 1, with monotone event counts and zero cells. It is not set to zero. |
| Top | [up, increment(up, X), increment(X, charm), increment(charm, top)] | `declared_top_tower` | The same missing X remains a parameter. |

`declared_lepton_costs`, `declared_down_costs` and `declared_up_costs` prove the cost sums.

| Family | Exact inheritance | Break in the pattern |
| --- | --- | --- |
| Lepton | Muon leading term = sigma*Delta times unit cost. Tau core latency = muon leading term, with a negative sign in tau (`declared_tau_signed_inheritance`). | Multipliers change from sigma to chi. Tau does not inherit muon's spin/feedback terms. Its incremental residual cancels them (`declared_tau_increment_residual`). |
| Down | Leading terms are D*Delta^n/eta for n=0,1,2 (`declared_down_leading_powers`). Full costs obey the corrected recurrence `declared_down_full_inheritance`. | Corrections are sigma, chi*sigma and Delta^2*chi/sigma, not one repeated series. |
| Up | Charm leading = Delta^2 times up leading divided by sigma−chi (`declared_charm_inheritance`); volume anchor = Delta times area anchor. | No level-1 species entry. Top drops eta and adds Delta^3/D, so it is not Delta times the diluted charm leading term (`declared_top_breaks_charm_scaling`). |

## What would force the next level?

For each proposed promotion, identify a required workload w(s,n,i), overhead, fixed period
and complete service. Prove that these jobs belong to the excitation and cannot be dropped,
shared away or delayed beyond the deadline. Identify one worker with a differing ring so
its service ceiling is 42 in that interval. If demand plus overhead exceeds 42, Rule 1
excludes a one-loop realization. It does not construct the larger schedule or its depth.

| Species | Declared target level | Promotions whose workload is missing | What is known |
| --- | ---: | --- | --- |
| Unit/electron | 0 | No promotion asserted. | One-reversal base account; no physical species identification. |
| Muon | 1 | 0→1 | Declared footprint and exact tower identity. |
| Tau | 2 | 0→1, 1→2 | Signed leading-term inheritance. |
| Up, down | 0 | No promotion asserted. | Declared point ledgers. |
| Strange | 1 | 0→1 | Geometric leading series only. |
| Charm | 2 | 0→1, 1→2 | Unknown intermediate level X remains explicit. |
| Bottom | 2 | 0→1, 1→2 | Declared two-step ledger tower. |
| Top | 3 | 0→1, 1→2, 2→3 | Declared volume ledger; unknown level X. |
| Neutrino | Unassigned | All species-specific promotions. | Declared tier set only; no selected footprint. |

Occupancy, metadata size and service work are distinct.
No species-specific overload is proved.

## Draft tier claims and generation orbits

Paper V's `2_ie_dynamics.tex` says linear/areal/volumetric quark generations. The current
Lean ledger instead declares up tiers {0,2,3} and down tiers {0,1,2}. These statements are
not reconciled here. `4_pmns_matrix.tex`'s lepton-axis 1+2 statement is a reference symmetry
with stated premises. It does not prove nesting depth, maintenance rate or a tier map.

The raw clock-root stabilizer has a singleton/pair key partition. The oriented channel
placement can reject that swap (`ClockSymmetry`, `FullGenerationOrbits`). No distinguishing
symmetry is sought in this step, and no generation key is assigned to a ledger entry.

## Programs and pillars

`EPSpine.programs_card` counts three generations times five visible classes: 15 witness
indices. Visible channel labels are a different 15-element set. The ring results are
level-0 infrastructure, not a classification of complete nested fermions.

## Mass as reversals per period

`ReversalEvents.registrations_eq_reversals` holds for arbitrary firing patterns. The old
witness has two total reversals and one differing-bit subtotal. Keeping the equal ring
quiet gives the unit-cost base account (`RetainedMap.quiet_program_cost`). This does not
identify the electron or prove full joint-state return in one clock period.

## Program dimension

`SpacetimeProgram` proves the registration ceilings and conditional packing bounds. A
fixed spatial clock line contains no spacetime root step (`execution_changes_space`).
Its box counts and `FootprintNoGo` reachability results are not nested service workloads.

## Footprint: what the generation can change

`FootprintNoGo` proves that common functionals of the preserving-root reachable set cannot
separate generations. The nested proposal must identify additional per-level work and
metadata; it does not reinterpret that result as a mass hierarchy.

## Generation orbits

`ClockSymmetry` certifies the full raw stabilizers; `FullGenerationOrbits` gives the
label-respecting obstruction. The level-role map uses neither as a tier selector.

## Generation readout needs vacuum contact: audit

The implication is not a consequence of current StrongMap. `GenerationReadoutContact`
shows that a preloaded request code can retain generation with one reversal; it does not
derive a physical encoder. Zero-key conservation is not unreadability. A zero-key lattice
intermediate has no supplied identification with a native stationary vacuum mode.
These results remain implementation constraints, not a flat minimization objective.

## Persistence of an isolated excitation

`ExcitationPersistence` and `JointSuccessorConstraints` state the missing admitted joint
execution and resource account for the parked renewal/decay work. Their module docstrings
keep the detailed audit. Closed-ring zero erasure does not prove reference renewal.

## Native cycle averages and the clock scale

The corrected return test permits even R over T ticks, with average `43*R/T`.
`AutonomousCensus` studies all 10 rules; its script exhausts all one-packet marker
states at odd n=3..13. Numerical cycle covers are computation, not Lean certificates.
Native all-n rate identities and the concrete n=43 witness are proved separately.

| Rule kind (two variants each) | At-rest candidate / other family | Period; reversals | Per 43 updates | Robust / Margin |
| --- | --- | --- | --- | --- |
| 0 | Static reflector gap d; single mirror has d=n. | 2d; 2 | 43/d; single mirror gives 1 at n=43. | Fails marker robustness; `mirror43_not_robust` certifies n=43. Single-mirror orbit visits n sites. |
| 1 | Circulating, no at-rest family found. | 2n; 0 | 0 | Marker-rate robust; not at rest. |
| 2,3 | Circulating in the finite census; primitive periods vary. | T; T/2 | 43/2 | Marker-rate robust at all n; n=43 winding not yet classified. |
| 4 | Two-site bounce at rest. | 4; 4 | 43 | Marker-rate robust, but saturated; `saturated_family_exceeds_margin`. |

Full tables and support counts are upstream in [PMKAutomaton](../PMKAutomaton/OVERVIEW.md#autonomous-native-cycle-census).
No stable unsaturated electron or charged-lepton family is selected. The old unit
window remains distinct from native return (`one_site_not_closed`). The common-window
average is ≤43 per one-packet ring (`native_average_bound`); two such accounts are ≤86,
even for long cycles. This does not identify any family with the lepton ratios.
AND/OR both reduce on ports to static kind 0 after retaining their scalar guard;
the full two-request/probe/phase receiver is outside the eight-state model. In the
fixed OR chart `(m,false)`, AND bypasses and is excluded; the AND chart is `(m,true)`.

| Clock statement | Status / exact consequence |
| --- | --- |
| Delta = 43 root updates | Proved count; no physical duration follows. |
| One root update takes kappa electron-time units | One shared supplied positive input, `ClockScale.TickDuration`; [SCOPE](../../SCOPE.md#named-premises). |
| Old PMAtoms/e8p E8 tick = 43 electron-time units | Legacy kappa=1 WHOLE-PERIOD block; not one receiver update. Numeric values unchanged. |
| Context rate=mass, unit electron rate, average one per Delta | Conditional `one_per_period_unit_rate` forces kappa=1/43; the context relation is not a PM premise. |
| Context unit rate with legacy kappa=1 | Requires 43 reversals/43 updates; incompatible with the strict differing-ring Margin ceiling (`differing_ring_margin_excludes_unit_rate`). |

No theorem fixes kappa. `electronTime` converts an electron time unit to SI seconds;
it does not identify a root update with that unit. EP and PMAtoms use the same supplied
clock API. No new physical calibration or e8p value is chosen.
Marker-rate robustness does not imply the old differing-ring Margin predicate.
Applying its ceiling to a physical dynamical-marker rule needs an identification proof.
Quark footprints remain composite-system work, not isolated colour persistence certificates.

## Conditional record comparisons (not physical mass)

`ChannelRecord` retains channel data in four bits; the coarse record already distinguishes
electron/up/down. `MapMaintenance.checks_once_cost` prices a SUPPLIED binary comparison.
An equally minimal Gray chart changes its Hamming cost (`encoding_changes_distance`).
Thus these distances are excluded as physical mass costs. They do not select native firing.
The exact reference-completion and generation-distance tables stay in the Lean certificates
(`reference_table`, `key_distances`); no reference completion is selected.

## Pillar classification of existing ledgers

This is arithmetic/label classification, not a derivation. C/M/P/G/T/R mean Capacity,
Map, Protocol, Governor, Toll, Margin. E means unit-price events with no automatic pillar
assignment. f marks a fractional price factor, not a whole count; role marks an explicit
docstring role, not a derived operation. Counts are distinct sourced slots in this audit;
"missing" means unassigned, not zero. No arbitrary residual is divided by a chosen price.
Direct pi*length and chi*coefficient identities use `LedgerPillars.pi_length_price` and
`boundary_factor_price`.

| Ledger | Assigned terms | E / unassigned terms | Slots present / missing | Frozen e8p pull |
| --- | --- | --- | --- | --- |
| Electron | T(operation): one reversal, price 1 | No other physical charge derived | 1 / C M P G R | Unit; unscored |
| Muon | M: -chi; C(f): -2*pi | E: sigma*Delta; feedback unassigned | 2 / P G T R | -2.40 sigma |
| Tau | M: chi*Delta^2 and -chi | -sigma*Delta; -D unassigned | 1 / C P G T R | -2.00 sigma |
| Up | None | D/eta | 0 / C M P G T R | -1.45 sigma |
| Down | None | D/eta + sigma/eta | 0 / C M P G T R | -1.05 sigma |
| Strange | M(f): chi*sigma/eta | D*Delta/eta | 1 / C P G T R | +0.05 sigma |
| Charm | None | D*Delta^2/(eta*(sigma-chi)) | 0 / C M P G T R | -1.25 sigma |
| Bottom | M(f): Delta^2*chi/(sigma*eta) | D*Delta^2/eta | 1 / C P G T R | -0.20 sigma |
| Top | C(role): Delta^3/D capacity leak | D*Delta^3 anchor | 1 / M P G T R | +0.35 sigma |

Pulls are the read-only reporter's signed midpoint pulls (2026-11-27); its interval widths
also matter. Light-quark comparisons use the supplied MS-bar/2-GeV convention, not an
isolated-particle mass measurement. No theorem matches occupancy cost to that scheme/scale.
The other quark rows are the reporter's own frozen references, not all 2-GeV quantities.
No selected neutrino footprint exists, so there is no neutrino row to classify.

`LedgerPillars.explicitSlots` tests whole baseline coefficients after expanding cells:
muon/tau have only Map, quarks and the event unit have none, a pure cell has all six.
The broader table also records fractional identities and documented roles. Support is
not determined by scalar value (`price_support_not_determined_by_value`). Current ring
pillars do not force six nonzero prices (`ring_pillars_do_not_force_six_prices`). The selected pulls are correlated diagnostics with different reference precision. They do
not establish a universal six-term law. In particular no two missing muon corrections
are identified: Toll/Margin have no named prices, but Protocol/Governor are unassigned too.
The withdrawn flat baseline-Toll lead is recorded in the `LedgerPillars` docstring.

Composite systems (PMHadrons); not comparable with elementary ledgers.

## Charges

The canonical rule is `PMConstants.Hypercharge.electric`: `blAxis / 2 + t3Sign`.
The axis and sign are the carrier premises in SCOPE. A numerical charge table is
not an extra species input. Antiparticle charges reverse the species sign.

| Encoding | Charge source | Agreement result |
| --- | --- | --- |
| Packet | `ColourRouting.electric` calls the canonical rule on the carried packet. | `CarrierChannels.electric_transport` |
| EP channel | `CarrierChannels.electric` calls the same rule on its axis and sign. | `CarrierChannels.packet_charge_eq` concerns hypercharge, not electric charge. |
| Base protocol | `ProtocolInventory.BaseProtocol.charge` supplies axis and sign. | `ProtocolInventory.base_charge_values` checks the four outputs. |
| Species | `CarrierSpecies.charge` reads its base protocol. | `channelSpecies_charge` |
| Final state | `FinalStateBridge.DecaySpecies.charge` reads species and sign. | Charge conservation in `FinalStateBridge` and `SubstrateFinalStates`. |
| Channel ledger | `ChannelParticleLedger.channelCharge` reads the EP channel. | `channelCharge_eq_Q` |
| Carrier amplitude | `CarrierCouplings.amplitude` uses rational charge times `sqrt alpha`. | `neutrino_em_zero` |
| Charged W | `TopTransition.Boson.charge` uses the doublet charge difference. | The exact rational difference is one. |
| Electromagnetic coupling | `ChainCouplings.electromagneticCouplingSquared` is a squared coupling. | It is not a charge. |

## Mass via OccupancyCost

Fermion masses use one scalar reading: `PMSubstrate.OccupancyCost.cost`.
The canonical counts and residuals are in `PMSubstrate.SpeciesFootprints`.
The [single footprint table](../PMSubstrate/OVERVIEW.md#occupancy-footprints)
records their status. Counts are whole numbers. A residual records a term for which
no whole pillar count has been supplied. It is not evidence for a persistent region.

| Particle | Declared tier label | Canonical footprint | Checked result | Open count |
| --- | --- | --- | --- | --- |
| Electron | Point | `OccupancyCost.Footprint` with `events := 1` | One event costs one electron unit. | Physical point-region identification. |
| Muon | Line | `SpeciesFootprints.Lepton.muonFootprint` | `LeptonMasses.muon_value`, feedback fixed point. | Sweep, attachment, residual and feedback rule. |
| Tau | Area | `SpeciesFootprints.Lepton.tauFootprint` | `LeptonMasses.tau_value` | Area attachment, multiplicity and inherited line. |
| Up, down | Point | `SpeciesFootprints.Quark.upFootprint`, `downFootprint` | `QuarkMasses.up_value`, `down_value` | Region, dilution and overhead. |
| Strange | Line | `SpeciesFootprints.Quark.strangeFootprint` | `QuarkMasses.strange_value` | Region, multiplicity and charges. |
| Charm, bottom | Area | `SpeciesFootprints.Quark.charmFootprint`, `bottomFootprint` | `QuarkMasses.charm_value`, `bottom_value` | Region, multiplicity and residuals. |
| Top | Volume | `SpeciesFootprints.Quark.topFootprint` | `QuarkMasses.top_value` | Region and fractional leading correction. |
| Neutrino | Declared tiers | No selected footprint. | `TierLedger.neutrinoTiers` checks the declared list. | Occupied region and output. |

`PersistencePremises.causal_cone_card` proves the square-region count. It does not
identify a species with that region or force a nesting level. Point/line/area/volume
are labels for the declared leading powers. The nested proposal must derive the
per-level work and architecture before checking `TierLedger.tiersFor`. The physical
unit, one clock event costs one electron mass, is a named premise in SCOPE.

`KoideSplit` checks an algebraic norm split; `KoideSelection` uses a supplied generation
record. Neither derives a footprint or Fourier phase. Working notes are in their docstrings.

## Record comparisons and heavy flip flag costs

| Topic | Lean modules | Checked result | Input still supplied |
| --- | --- | --- | --- |
| Exact record | `RecordCoordinates`, `RecordEncoding`, `RecordPortIdentification` | Finite coordinates and embedding identities. | Physical register identification. |
| Receiver trace | `IsolatedExcitation`, `IsolatedReceiverTrace`, `RingSurvivors` | Occupancy, registration counts and finite-ring bounds. | Initial requests and occupied traffic. |
| Writer | `HeavyFlipRecords`, `ElectricHeavyRecord`, `ElectricFourPortRecord` | Record writes and flag sums under the given guards. | Admitted pulse, seed and reuse. |
| Setup | `ElectricCompanionSetupFlagCosts`, `ElectricPrimitiveFlagCosts` | Primitive word and companion setup costs. | Physical availability of the bank. |
| Current | `ElectricChiralKick`, `ElectricCoordinateDecoder` | Conditional current and decoder words. | Timings and preparation. |
| Protocol flags | `ProtocolFlagCosts`, `WireReferenceCost` | Static constraints and factorized writer costs. | Sampling and reset contract. |
| Schedule | `WireSchedule` | Serial placement and costs including the supplied remainder. | Admission, traffic, reset and tariffs. |
| Insertion | `ChargedInsertion`, `GappedGluedCrossing` | Conditional operators and crossing identities. | A link from execution to occupied footprint. |

### Charged density and wall leakage

`PMAction.WallRestChirality` checks static density and readout identities. It does not select
an occupied trace. The `ExternalStates` docstring contains the comparison audit. The
`WireSchedule` and `PolarMeasure` docstrings hold schedule and continuum notes.

## Decay and widths

The shared survival and positive-rate mean-life API is `PersistenceMechanics.Rates`.
EP supplies physical adapters. Stable zero-rate configurations do not receive a
zero mean life from a reciprocal convention.

| Topic | Module or declaration | Checked result | Supplied input |
| --- | --- | --- | --- |
| Routing | `ProtocolDynamics`, `SubstrateFinalStates`, `FinalStateBridge` | Charge-conserving finite descent and final-state bridges. | Physical final-state choice. |
| Survival | `DecayLaw`, `Survival`, `MeanLife` | Finite-tick law and continuum relation; shared constant hazard. | Persistence premises and rate. |
| Finite channels | `RateModel`, `BetaLattice`, `LeptonLattice`, `LeptonLifetime` | Finite mode sums and positive-rate lifetimes. | Mode set, support and scale. |
| Weak vertex | `WExchangeRate`, `VATrace` | Contact limit and spin trace. | Physical current and flux identification. |
| Massless width | `MuonRate.muon_rate` | `G² m⁵ / (192 pi³)` from the contact amplitude and measure. | Contact interaction, external states and flux. |
| Massive width | `MassiveWidth.closed_width` | Exact daughter phase factor. | Physical daughter and parent assignment. |
| Measure | `PairSphere`, `PairTensor`, `PhaseSpace`, `PolarMeasure` | Angular, radial and energy-shell integrals. | Physical scale and support. |
| Muon tree | `MuonLifetime`, `PhysicalUnits` | E8 masses and canonical Fermi coupling give the tree width. | Fermi/VEV premises and SI unit anchors. |
| Muon correction | `MuonLifetimeCorrected`, `MuonQEDLoops`, `MuonLifetimeHigherOrder` | Certified intervals for supplied QED formulas. | QED coefficients and leptonic running law. |
| Tau scaling | `TauLifetime.tau_lifetime_tree` | Transports supplied muon-time and branch intervals. | Muon time and electronic branch. |
| Tau E8 | `TauE8.tauLifetimeE8_bounds` | Branch-conditional lifetime from E8 muon width. | Electronic branch. |
| Tau correction | `TauLifetimeCorrected.tau_lifetime_corrected` | Corrects the supplied tree interval by phase, W and QED factors. | Supplied correction formulas; E8 running at both scales. |
| Neutrino comparison | `NeutrinoContext` | Floor-scale enclosures and conditional exclusion tests. | Supplied comparison window; e8p instantiates it. |
| Tau branches | `TauBranching.phase_bounds`, `parton_level`, `supplied_needs` | Leptonic phase ratio and branch/hadronic-factor relation. | Inclusive hadronic factor. |

## Supplied inputs and premises

Measured values belong to `tools/e8p/E8PConstants/Experimental.lean`.
The reporter supplies the tau electronic branch and, for the scaled-muon row,
the measured muon time. The tau running coupling uses `MuonQEDLoops.runningAlpha`
at the E8 tau mass. It has no measured running-coupling anchor. This is the same
supplied leptonic running model used at the muon scale, not a complete threshold model.
The van Ritbergen–Stuart series is supplied theory, not a measurement or a PM derivation.

## EP premise ledger

[SCOPE](../../SCOPE.md#named-premises) supplies the named rows; local inputs enter at the layers below.

| Layer | Lean location or SCOPE row | Status |
| --- | --- | --- |
| Substrate | SCOPE · `ClockAlignment` | Named placement premise. `alignedSectorBasis_eq` checks the explicit placement. |
| Substrate | SCOPE · Lorentzian signature and complex amplitudes | Named model premises. Root moments through degree four are PM theorems. |
| Substrate | `ChannelPlacement.channelE8`, `referenceClass_eq_clock` | Proved from PM. |
| Substrate | `PMConstants.Values.alpha`, `PMConstants.Values.fermi 1` | PM coupling and conversion formulas. The Fermi value inherits the SCOPE VEV structure. |
| Substrate | `SharedUnits.me`, `PhysicalUnits.electronTime` | PM conversion at the external SI unit anchors. |
| Node | SCOPE · `ClockSites`, `RingReceiver.tick` | Named tick-to-root identification. The finite clock and ring movement are checked. |
| Node | SCOPE · `ClockTickWeights`, `Machine.SliceHop` | Named closure premise. The discrete orbits are checked. |
| Node | SCOPE · `PMKAutomaton.Interface` | Named admission, geometry, resources, booking, traffic and tariff inputs. See the [upstream closeout](../PMKAutomaton/OVERVIEW.md#kautomaton-closeout). |
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
| Carrier | `LinkGapLaw.gapA`, `LinkGapLaw.gapB` | Supplied alternatives for matching `yv` to detuning. The `κ_τ` measurement is an e8p comparison. |
| Protocol | SCOPE · `MapMaintenance.ChecksOnce` | Named check-frequency premise. Record, full reference, native readout and realized schedule remain open. |
| Protocol | SCOPE · `WireSchedule.Premises` | Named serial route and admitted bookings. |
| Protocol | SCOPE · `WireReferenceCost`, `PMKAutomaton.Values` | Named population and reset contract. The threshold arithmetic is proved. |
| Protocol | `EPSpine.spine`, `EPSpine.witnessAt_registrations` | Proved for class witnesses. Closure of a complete occupied program is open. |
| Protocol | SCOPE · `TierLedger.tiersFor` | Named tier lists. The wire address assignment remains an explicit input. |
| Protocol | `LeptonMasses.muon`, `LeptonMasses.tau` | Canonical species footprints with supplied counts. The invariant values and arithmetic follow from PM. |
| Protocol | `QuarkMasses.up` through `QuarkMasses.top` | Canonical species footprints with supplied counts. The invariant values and arithmetic follow from PM. |
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
| Protocol | `TauLifetimeCorrected.qedTau` | Supplied QED formula. `MuonQEDLoops.runningAlpha tau` uses the E8 baseline coupling. |
| Protocol | `TauLifetimeCorrected.wRatio` | SM finite-propagator correction applied with the E8 W mass. |
