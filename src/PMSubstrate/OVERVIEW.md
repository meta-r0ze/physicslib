# PMSubstrate — overview of checked results

Lean 4 proofs for *Persistence Mechanics of the Quantum Vacuum I: The E8 Substrate and the
Fine-Structure Constant*.

## Main result

`PMSubstrate.Main.persistence_selects` (`PMSubstrate/MainTheorem.lean`): from the postulates below,

* the substrate lattice is **E8**, containing two orthogonal **D4** sectors;
* the clock period is **Δ = 43**;
* every integer input of the index is forced: D = 4, ν = 16, N = 32, σ = 5, χ = 2;
* the index, read as net transitions per cycle, is

  Z = 43π + 2 + 334/(32³·5·172) + 1/(31·6·43²) − 1/167 − 2/43,
  with 137.035999212381397211 < Z < 137.035999212381397213.

`PMSubstrate.Main.postulates_satisfiable`: E8 with the 43-cycle, one time direction and the sphere
satisfies every postulate, so the set is consistent. Comparison with measured α is separate
(`PMSubstrate.alpha_deviations`) and is not part of the theorem.

## Canonical constants and units

| Quantity | Canonical Lean name | Source |
| --- | --- | --- |
| α | `PMSubstrate.causalCoupling` | Reciprocal of the baseline index. |
| α⁻¹ | `PMSubstrate.geometricIndex` | Impedance at the baseline parameters. |
| Δ | `PMSubstrate.E8Values.Delta` | Baseline clock period. |
| Uniform event probability | `PMSubstrate.PersistenceEvents.uniformEventProbability` | Event cardinality divided by the sample-space cardinality. `NetCost.prob` delegates to it. |
| Toll price | `PMSubstrate.tollTerm` | Parametric impedance term. |
| Toll boundary | `TollSampleSpace`, `TollBoundaryWitness`, `embedTollBoundary`, `tollBoundaryEvent` | Baseline sample, witness, embedding and event. `uniform_toll` proves the baseline probability equals the price. |
| General Toll event | `ProtocolToll.protocolTollSuccessEvent` | Parametric finite sample. |
| Physical root-tick duration | `ClockScale.TickDuration` | Supplied positive kappa; no calibration theorem. `legacyUnitTick` is the old candidate, not a selected physical scale. |
| SI conversions | `SIUnits` | One rational source for each family. `electronMassMeVRat_cast` relates the two MeV types. The EP lifetime module computes electron time from these units. |

## Postulates

| Postulate | PM requirement | Lean | Consequence |
|---|---|---|---|
| Bounded-cost sets are finite | Finiteness | `Vacuum.Geometric.finite` | positive definite (`Translation.posDef_iff_finite_levels`) |
| Every one-bit distinction is readable by the substrate itself | Conservation, Closure | `Vacuum.Geometric.readable` | odd determinant (`SelfReadable.bitReadable_iff_odd`) |
| Glue elements are bits, 2Λ* ⊆ Λ | Map | `Vacuum.Geometric.bitAddressed` | with the above, unimodular |
| A nontrivial exchange law in which zero-pairing operations commute | Protocol, Causality | `Vacuum.Geometric.exchange` | even (`OrthogonalExchange.orthogonal_nontrivial_exchange_forces_even`) |
| Least rank among substrates meeting the above | Economy (PM selection) | `Vacuum.Economical` | rank 8, then E8 (`RankEight.rank_dvd_eight`, `E8Unique.e8_unique`) |
| Two orthogonal irreducible bit-addressed rank-4 root sectors | Postulate B | `Vacuum.SectorPostulates` | D4 (`Sectors.sector_selection`) |
| Clock = a substrate plane; states = its discriminant group; unique geometry; gap-only observations | Closure, Map, Causality | `Vacuum.ClockPostulates` | Δ = 43 (`Vacuum.vacuum_selects`) |
| Volume element squares to −1 | Postulate G | `Derived.SignaturePostulate` | one time direction |
| Boundary of least topological complexity | Economy (Postulate H) | `Derived.BoundaryPostulate` | sphere, χ = 2 |

`Vacuum.geometric_iff`: the first four postulates hold exactly for positive-definite, even,
unimodular, nonzero lattices. `VacuumIndependence` gives, for each postulate, a lattice meeting
every other one but not that one (hyperbolic plane, D4, A2, ℤ, E8 ⊕ E8).

`Channels.sectorBasis` is one placement of the two D4 sectors; it is not clock-aligned.
`PMKAutomaton.AlignedSectors.alignedSectorBasis` is the clock-aligned placement with the same
`d4d4` Gram matrix (`aligned_d4d4`).

## The six terms

Each term is an expected number of transitions per cycle (`NetCost.expected_count_linear`,
unit toll by Closure). Provisioning pillars add; Protocol and Governor, defined by restricting and
coordinating other transitions, subtract (`NetCost.removal_subtracts`, `NetIndex.signs`).

| Term | Value | Meaning | Main theorems |
|---|---|---|---|
| Capacity | 43π | largest boundary a causal cycle allows, any shape; only distinctions cost | `Capacity.capacity_is_max`, `Capacity.barbier`, `Distinctions.only_distinctions_cost` |
| Map | 2 | full 2π turns of the boundary to close (Gauss–Bonnet) | `Descartes.descartes`, `Derived.boundary_sphere` |
| Protocol | −1/167 | the one successor among the residual addresses | `PersistenceEvents.protocol_persistence`, `TollFilters.residual_card` |
| Governor | −2/43 | the boundary's turns spread uniformly over the cycle | `ImpedanceTerms.governor_uniform` |
| Toll | 334/(32³·5·172) | a transition that preserves identity, orientation and non-aliasing | `PersistenceEvents.toll_persistence`, `PersistencePremises.toll_identity`, `Arity.three_legs_interact`, `Orientation.two_orientations` |
| Margin | 1/(31·6·43²) | one configuration among description × local tree × causal cone | `FinalPremises.description_minimal`, `ImpedanceTerms.tree_vertices`, `PersistencePremises.causal_cone_card` |

Uniform measures come from Closure (`ClosureSymmetry.invariant_measure_uniform`).

**Not derived inside Lean:** the postulates above, and PM's definitions of the pillars (Governor
restricts transitions, Protocol coordinates them; a vertex sees only local observations, which is
Postulate I). See [`TODO.md`](TODO.md) for the missing implications.

## Occupancy footprints

`OccupancyCost.cost` prices whole clock events at one and full cells at the
baseline impedance. Extra pillar charges are signed integers. A fixed
residual gives only countably many possible costs
(`countable_costs_at_residual`, `exists_not_cost_at_residual`).

The table records the declared species ledgers. Quark events are the whole
part of the overhead-adjusted leading term, with colour dilution for charm.
The top uses the whole part of its full volume term. The remaining charges
stay in the residual. The causal cone has `Δ² = 1849` events. Using that cone
for an occupied nucleon is the ledger assignment.

The intervals are rounded outwards. They use exact rational arithmetic,
Mathlib's 20-decimal π bounds and rational bounds on √2 from squaring.
The share is signed and is given as a percent. A zero entry is exact.

| Particle | Events | Cells | Extra pillar counts | Residual enclosure (mₑ) | Residual / total |
| --- | ---: | ---: | --- | ---: | ---: |
| Electron | 1 | 0 | — | 0 | 0% |
| Muon | 215 | 0 | Map −1 | [−6.231729, −6.231728] | [−3.013871, −3.013870]% |
| Tau | 3483 | 0 | Map −1 | −4 | [−0.115042, −0.115041]% |
| Up | 4 | 0 | — | [0.023391, 0.023392] | [0.581395, 0.581396]% |
| Down | 4 | 0 | — | [5.052631, 5.052632] | [55.813953, 55.813954]% |
| Strange | 173 | 0 | — | [10.064327, 10.064328] | [5.497699, 5.497700]% |
| Charm | 2479 | 0 | — | [0.750487, 0.750488] | [0.030264, 0.030265]% |
| Bottom | 7439 | 0 | — | [744.176608, 744.176609] | [9.093982, 9.093983]% |
| Top | 337904 | 0 | — | 0.750000 | [0.000221, 0.000222]% |
| π⁰ | 0 | 2 | Map −5 | [0.071428, 0.071429] | [0.027041, 0.027042]% |
| π⁺ | 0 | 2 | Map −5 | [9.060482, 9.060483] | [3.317248, 3.317249]% |
| K⁰ | 0 | 7 | — | [14.551201, 14.551202] | [1.494265, 1.494266]% |
| K⁺ | 0 | 7 | — | [6.848317, 6.848318] | [0.708861, 0.708862]% |
| Proton | 1849 | 0 | Toll 5 | [−12.847386, −12.847385] | [−0.699691, −0.699690]% |
| Neutron | 1849 | 0 | Toll 3, Margin −1 | [−10.316371, −10.316370] | [−0.561074, −0.561073]% |

## Layout

| Path | Contents |
|---|---|
| `PMSubstrate/MainTheorem.lean` | main theorem and satisfiability |
| `PMSubstrate/Vacuum.lean`, `VacuumIndependence.lean` | postulates, E8 and clock selection, independence |
| `PMSubstrate/Lattices`, `RankEight`, `ThetaE8`, `E8Unique`, `Translation*`, `Postulates`, `ClaimBoundary` | lattice classification: theta series, rank divisible by 8, uniqueness of E8 |
| `PMSubstrate/Clock`, `ClockPlane`, `DiscriminantGroup`, `Scheduling`, `Selection`, `ClassNumber`, `ScheduleReconstruction`, `ScheduleReconstructionField` | clock, schedule window (the no-adjacent-idle hypothesis of the older route is discharged from gap-only reconstruction in `ScheduleReconstruction`), class number one |
| `PMSubstrate/SelfReadable`, `Parity`, `OrthogonalExchange`, `Sectors`, `Channels`, `ChannelSymmetry` | unimodularity, evenness, sectors, channels; the uniform channel measure from E8 symmetry |
| `PMSubstrate/DerivedParameters`, `E8Invariants`, `CapacityBarbier`, `CapacityEnvelope`, `CauchyPolygon`, `CircleLength`, `Distinctions`, `Descartes`, `TollFilters`, `ClosureSymmetry`, `PersistenceEvents`, `PersistenceMaximin`, `PersistencePremises`, `FinalPremises`, `NetCost`, `NetIndex`, `Impedance*`, `ProtocolToll` | parameters and the six terms |
| `PMSubstrate/E8Values.lean` | canonical E8 record names `D, Δ, ν, σ, χ, R_M, N`, the derived loads, and `overhead`; exported by the `PMSubstrate` root |
| `PMSubstrate/Pillars`, `Comparison`, `PhysicalBridge` | PM failure modes, Postulate R, and conditional physical bridge lemmas |
| `PMSubstrate/SIUnits` | the single source for unit conversions (CODATA 2022 `m_e`, exact `ħc` and `c`); `m_e` is the mass unit by proof (`scale_no_unique_min`), not a prediction |
| measured α comparisons | moved to the e8p layer (`E8PConstants.ExperimentalComparison`); not part of the axiom-checked tree |
| `PMSubstrate/Research/` | alternative routes, counterexamples and necessity tests (not on the main path) |
| `../classification/` | vendored class-number-one proof (Peter W. Murphy, Apache-2.0) |
| `../audits/` | scoped axiom audits for the research modules |

## Build and audit

Lean 4.34.1, mathlib `d13f23b` (pinned in `lake-manifest.json`). With
[elan](https://github.com/leanprover/elan):

```sh
lake exe cache get
./build.sh PMSubstrate
```

`./build.sh PMSubstrate` builds the library. `./build.sh audit` runs the whole-tree strict audit
(`AuditStrict.lean`: every project declaration may depend only on `propext`,
`Classical.choice`, `Quot.sound`), the readable/import audit, and the class-number audit. The
negative tests for the strict audit live under `tools/`.

## Credits

The class-number-one classification in `../classification/` is Peter W. Murphy's formalization
(https://github.com/DrMurphyIsIn/tenth-discriminant), vendored unmodified; see its NOTICE and
PROVENANCE. Built on mathlib.
