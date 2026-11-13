# PMAction/Machine — overview

The native E8 finite machine: reversible constructions over the substrate's
carrier/register/reference/record state, with exact all-state readout. Entry
points are theorem names, not exhaustive lists.

## Base dependency
`PMSubstrate` only (`Channels`, `ChannelSymmetry`, `Lattices`, `NetCost`,
`PersistenceEvents`, `E8Values`) — no `PersistenceMechanics`, no other paper.

## Areas

| Area | Modules | Result and retained inputs |
| --- | --- | --- |
| Carriers and events | `CarrierEvents`, `CarrierParity`, `CarrierWeyl`, `CarrierClifford`, `CarrierVacuumSector`, `CarrierVacuumEvolution`, `CarrierReadoutQuotient`, `CarrierResponse` | D₄ glue-class carriers, reversible reflection events, the antipodal-odd physical sector (`range_iff_odd`), native generators and full-Hamiltonian intertwining. Physical class/wall allocation, observation and cross-sector coupling remain inputs. |
| Registers and readout | `IndependentRegisters`, `RegisterPrograms`, `RegisterHamiltonian`, `RegisterVacuum`, `RegisterInteraction`, `RegisterSplit`, `RegisterControl`, `RegisterReference`, `ChiralRegisterCurrent`, `ReadoutAdditivity`, `CarrierProbe`, `MatchedLatticeProbe`, `ScheduledReadout`, `ParityReadoutCircuit`, `InBandRootReadout`, `InterferenceReadout` | Boolean register banks with exact tensor readout; occupation-dependent hops; the full native generator/readout, four-phase clock and joint controls. Banks, preparation, amplitude and admission are supplied. |
| Roots and reference | `RootTransfer`, `RootTransferPhase`, `RootTransferAccounting`, `RootBranchEncoding`, `RootPulseEvents`, `ActualRootRepair`, `RootOrderComparison`, `RootReferencePreparation`, `ReferenceSourceBoundary`, `NativeCarrierProtocol`, `NativeCarrierState`, `NativeReferenceBackground`, `FullCarrierIdentification`, `ReferenceSampling`, `SummedReference`, `ReferenceWalkParity` | Lazy statistical root transfer, restoring words, stationary-reference classification, one-hot lift and conditional minimization. Physical preparation and source contracts remain inputs. |
| Records and supply | `RecordTransport`, `WalkRecordTransport`, `RecordSupply`, `RecordFeedbackBoundary`, `PrimitiveRecordBoundary`, `OpenReferenceFlow`, `WalkReferenceCoupling`, `WalkReferenceProtocol`, `WalkReferenceCycle`, `RootWalkEncoding`, `RootCarrierWalk`, `RootCarrierCycle`, `WalkSpeed` | Exact FIFO retention, `live_at_site`/`clean_supply`/`open_orbit_forever`, and finite ring return. An indefinite source is not derived from closed finite-memory persistence (`OpenReferenceFlow`). |
| Clock | `ClockPeriod`, `ClockDynamics`, `ClockControlledRoot` | The period is the substrate `Δ = E8Values.Delta` (`ClockPeriod.Delta`); the four-phase schedule is unitary on coherent clock amplitudes (`ClockDynamics`). Physical calibration and primitive prices remain inputs. |
| Native packet / locality | `NativePacketUpdate`, `NativePacketRouting`, `NativePacketLinks`, `NativeCoherentLinks`, `NativeLocalityBoundary`, `NativeRootGenerators` | The native E8 packet subsystem's transport/continuity contracts and finite-range boundary. Admission holds under `Admission`'s rule (`native_conserving`, `native_local`). |
| Refresh events | `RootMaintenance` | The reference-maintenance task model's swap is a root reflection on a two-carrier cell at the job's site (`encode_swap`, `event_is_root`); the minimal restoring schedule is one root event per required resource (`canonical_is_root`). |
| Repair events | `FactorRepair` | A root event acts in one non-abelian factor and the abelian phase rides on its amplitude, so a repair needs an event per displaced factor (`events_ge`) and Economy takes exactly that many (`repair_least`). On a colour and weak singlet any root event acts through its phase, so the singlet's repair is one event (`singlet_least`). Premise: a displacement in one factor is undone by one event. |
| The microscopic hop | `AxisHop`, `SliceHop`, `CarrierRootGate` | An axis step `2eⱼ` is not a root; it is a word of two roots, six of them (`axis_words_count`). Within a tick the hop is the equal-weight sum of the four in-slice words (one orbit of the slice symmetries); the other two each run the clock backwards for one event (`slice_uniform`, `clock_words_reverse`). The comparison gate's coherent step is one root reflection run for a quarter period (`root_gate_unitary`). |
| Controls from the substrate | `ConstantControls`, `ProfileControls`, `RootWordControls`, `EdgeLocality`, `ConfigurationControls`, `D4EdgeSeparation` | The C² control one-forms are the gauge-field configuration (rates of the root-cost generators), and they follow from the substrate's links. Homogeneous links come from constant controls; a site-varying rate along one generator from a smooth profile; an ordered root word `exp R₀ · exp R₁ · exp R₂ · exp R₃` on one edge from staggered profiles in its middle half. An edge's link depends only on the controls along it, smooth Urysohn bumps glue the edges, and the middle of a `D₄` edge misses every other edge (a mixed reversal would give odd coordinate sum). So every finite configuration of distinct `D₄` edges, each with its own root word, is realized by one set of C² controls (`d4_configuration_realized`). |
| Continuum premises from the substrate | `NativeConsistency`, `CompactLimits` (with `PMAction.CompactTransport`) | Transports of a compactly supported C² connection are cubically consistent with it and it is `C^{1,1}`. A smooth cutoff gives the configuration's controls compact support, so the substrate's configurations meet those premises (`d4_configuration_consistent`). `ref_limit_c2`, `sum_limit_c2`: the reference-sampled limits with the links as transports, no separate consistency premise. |
| Matter in the continuum | `MatterContinuum` (with `PMAction.ScalarTransport`) | `scalar_limit_c2`: for the transports of a compactly supported C² connection and a compactly supported C² field, the event-priced scalar density converges to `Z_φ Σ_μ ‖(∂_μ + A_μ)Φ‖²` with no further premise. `spinor_hop`: a spinor hop weighted by `Γ` is `h·Γ(∂_v + A_v)Φ + O(h²)`. So the substrate's scalar and spinor fluctuations carry the continuum operators `−D²` and `γ·D` whose spectra `RunningResponse` uses. |

## Interpretation boundary
Build success certifies the conditional reversible constructions, not physical
identification. **Supplied:** banks/occupancies, amplitudes, the *payload* charge
operator, preparation of the initial reference, gate admission, clock calibration
and the price *scale*.

**Derived** E8/persistence content: carrier parity (statistics), the reference
chirality and charge (`ReferenceAnchor.reference_charges`), the clock period
(`ClockPeriod.Delta`), the exact maintenance/supply identities, the substrate's
unboundedness from persistence (`HomogeneousRouting.forever_iff_open`,
`forever_needs_infinite`) and the minimum-execution cost
(`ReferenceMaintenance.minimum_executable_cost`).
