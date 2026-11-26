import PMKAutomaton.Machine.WalkSpeed
import PMKAutomaton.Machine.InterferenceReadout
import PMKAutomaton.Machine.CarrierEvents
import PMKAutomaton.Machine.CarrierCost
import PMKAutomaton.Machine.CarrierResponse
import PMKAutomaton.Machine.BranchPulseContract
import PMKAutomaton.Machine.RefreshSchedule
import PMKAutomaton.Machine.ReferenceMaintenance
import PMKAutomaton.Machine.CoherentRecordRestoration
import PMKAutomaton.Machine.CoherentRefresh
import PMKAutomaton.Machine.RecordTransport
import PMKAutomaton.Machine.WalkRecordTransport
import PMKAutomaton.Machine.WalkReferenceCoupling
import PMKAutomaton.Machine.WalkReferenceProtocol
import PMKAutomaton.Machine.WalkReferenceCycle
import PMKAutomaton.Machine.OpenReferenceFlow
import PMKAutomaton.Machine.PrimitiveRecordBoundary
import PMKAutomaton.Machine.CoherentPreparation
import PMKAutomaton.Machine.AxisHop
import PMKAutomaton.Machine.SliceHop
import PMKAutomaton.Machine.ConstantControls
import PMKAutomaton.Machine.ProfileControls
import PMKAutomaton.Machine.RootWordControls
import PMKAutomaton.Machine.FiniteRootWordControls
import PMKAutomaton.Machine.FiniteConfigurationControls
import PMKAutomaton.Machine.EdgeLocality
import PMKAutomaton.Machine.ConfigurationControls
import PMKAutomaton.Machine.D4EdgeSeparation
import PMKAutomaton.Machine.NativeConsistency
import PMKAutomaton.Machine.CompactLimits
import PMKAutomaton.Machine.MatterContinuum
import PMKAutomaton.Machine.FactorRepair
import PMKAutomaton.Machine.RootMaintenance
import PMKAutomaton.Machine.CarrierRootGate
import PMKAutomaton.Machine.ReferenceClassHop
import PMKAutomaton.Machine.RecordFeedbackBoundary
import PMKAutomaton.Machine.CarrierReferenceCycle
import PMKAutomaton.Machine.CarrierProbe
import PMKAutomaton.Machine.ClockControlledRoot
import PMKAutomaton.Machine.MatchedLatticeProbe
import PMKAutomaton.Machine.ScheduledReadout
import PMKAutomaton.Machine.ReadoutGateBoundary
import PMKAutomaton.Machine.ParityReadoutCircuit
import PMKAutomaton.Machine.InBandRootReadout
import PMKAutomaton.Machine.RootTransfer
import PMKAutomaton.Machine.RootTransferPhase
import PMKAutomaton.Machine.RootTransferAccounting
import PMKAutomaton.Machine.RootBranchEncoding
import PMKAutomaton.Machine.RootPulseEvents
import PMKAutomaton.Machine.ActualRootRepair
import PMKAutomaton.Machine.RootWalkEncoding
import PMKAutomaton.Machine.RootCarrierWalk
import PMKAutomaton.Machine.RootCarrierCycle
import PMKAutomaton.Machine.RootReferencePreparation
import PMKAutomaton.Machine.ReferenceSourceBoundary
import PMKAutomaton.Machine.NativeCarrierProtocol
import PMKAutomaton.Machine.NativeCarrierState
import PMKAutomaton.Machine.NativeReferenceBackground
import PMKAutomaton.Machine.FullCarrierIdentification
import PMKAutomaton.Machine.CarrierParity
import PMKAutomaton.Machine.CarrierTriality
import PMKAutomaton.Machine.CarrierWeyl
import PMKAutomaton.Machine.SubstrateWeylRoots
import PMKAutomaton.Machine.OrthogonalRootPhase
import PMKAutomaton.Machine.OddCarrierPhase
import PMKAutomaton.Machine.CarrierVacuumSector
import PMKAutomaton.Machine.CarrierClifford
import PMKAutomaton.Machine.CarrierVacuumEvolution
import PMKAutomaton.Machine.CarrierReadoutQuotient
import PMKAutomaton.Machine.ReferenceWalkParity
import PMKAutomaton.Machine.NativeLocalityBoundary
import PMKAutomaton.Machine.ReferenceSampling
import PMKAutomaton.Machine.SummedReference
import PMKAutomaton.Machine.RecordSupply
import PMKAutomaton.Machine.HomogeneousRouting
import PMKAutomaton.Machine.ReadoutAdditivity
import PMKAutomaton.Machine.NativePacketLinks
import PMKAutomaton.Machine.NativePacketRouting
import PMKAutomaton.Machine.NativeRootGenerators
import PMKAutomaton.Machine.NativeCoherentLinks
import PMKAutomaton.Machine.NativePacketUpdate
import PMKAutomaton.Machine.CarrierClassBundle
import PMKAutomaton.Machine.IndependentRegisters
import PMKAutomaton.Machine.RegisterPrograms
import PMKAutomaton.Machine.RegisterHamiltonian
import PMKAutomaton.Machine.RegisterVacuum
import PMKAutomaton.Machine.RegisterInteraction
import PMKAutomaton.Machine.ChiralRegisterCurrent
import PMKAutomaton.Machine.ClockDynamics
import PMKAutomaton.Machine.RegisterSplit
import PMKAutomaton.Machine.RegisterReference
import PMKAutomaton.Machine.RegisterControl
import PMKAutomaton.Machine.RootOrderComparison
import PMKAutomaton.Machine.CoherentGate
import PMKAutomaton.Machine.GluedRegister
import PMKAutomaton.Machine.VectorEvenFrame

/-! Native E8 carrier, register and transport operations.

## Native machine map

The native E8 finite machine: reversible constructions over the substrate's
carrier/register/reference/record state, with exact all-state readout. Entry
points are theorem names, not exhaustive lists. It includes the native carriers,
registers, references, records, roots and clock, with their reversible update
and readout theorems.

The machine and the PMAction finite proofs share a build layer. Import
`PMKAutomaton.Machine` to use its full interface. Import an individual module to
use a smaller part of it. [Open work](TODO.md).

```sh
./build.sh lean PMKAutomaton.Machine.CarrierEvents
./build.sh fast PMAction
```

## Base dependency

The machine uses PMSubstrate's channel, lattice, clock and cost results. It
shares the PMAction build layer and uses its finite operator, dynamics and
comparison proofs. The [dependency audit](../AuditDependencies.lean)
keeps the machine upstream of PMConstants and packet transport.

## Areas

The native crossing entry points are `GluedRegister.crossing_word_glued` and
`CarrierTriality.glued_triality_step`. See the
[transport overview](OVERVIEW.md) for their role in a node handoff.

| Area | Modules | Result and retained inputs |
| --- | --- | --- |
| Carriers and events | `CarrierEvents`, `CarrierParity`, `CarrierWeyl`, `CarrierClifford`, `CarrierVacuumSector`, `CarrierVacuumEvolution`, `CarrierReadoutQuotient`, `CarrierResponse` | D₄ glue-class carriers, reversible reflection events, the antipodal-odd physical sector (`range_iff_odd`), native generators and full-Hamiltonian intertwining. Physical class/wall allocation, observation and cross-sector coupling remain inputs. |
| Even carrier records | `VectorEvenFrame` | Complete four-dimensional even pair basis of the actual vector carriers (`isometry`, `range_iff_even`), orthogonality to the odd contrasts, the coordinate stabilizer's `1 + 3` orbits, and explicit simple-root words writing its markers. These modes are stationary under the existing odd-compressed wall completion. |
| Registers and readout | `IndependentRegisters`, `RegisterPrograms`, `RegisterHamiltonian`, `RegisterVacuum`, `RegisterInteraction`, `RegisterSplit`, `RegisterControl`, `RegisterReference`, `ChiralRegisterCurrent`, `ReadoutAdditivity`, `CarrierProbe`, `MatchedLatticeProbe`, `ScheduledReadout`, `ParityReadoutCircuit`, `InBandRootReadout`, `InterferenceReadout` | Boolean register banks with exact tensor readout; occupation-dependent hops; the full native generator/readout, four-phase clock and joint controls. Banks and admission are supplied; the preparation circuit for the coherent state exists (`CoherentPreparation`), the physical input it acts on is supplied. |
| Roots and reference | `RootTransfer`, `RootTransferPhase`, `RootTransferAccounting`, `RootBranchEncoding`, `RootPulseEvents`, `ActualRootRepair`, `RootOrderComparison`, `RootReferencePreparation`, `ReferenceSourceBoundary`, `NativeCarrierProtocol`, `NativeCarrierState`, `NativeReferenceBackground`, `FullCarrierIdentification`, `ReferenceSampling`, `SummedReference`, `ReferenceWalkParity` | Lazy statistical root transfer, restoring words, stationary-reference classification, one-hot lift and conditional minimization. Physical preparation and source contracts remain inputs. |
| Records and supply | `RecordTransport`, `WalkRecordTransport`, `RecordSupply`, `RecordFeedbackBoundary`, `PrimitiveRecordBoundary`, `OpenReferenceFlow`, `WalkReferenceCoupling`, `WalkReferenceProtocol`, `WalkReferenceCycle`, `RootWalkEncoding`, `RootCarrierWalk`, `RootCarrierCycle`, `WalkSpeed` | Exact FIFO retention, `live_at_site`/`clean_supply`/`open_orbit_forever`, and finite ring return. An indefinite source is not derived from closed finite-memory persistence (`OpenReferenceFlow`). |
| Clock | `PMSubstrate.E8Values`, `ClockDynamics`, `ClockControlledRoot` | The period is the substrate `Δ = E8Values.Delta` (`PMSubstrate.E8Values.Delta`); the four-phase schedule is unitary on coherent clock amplitudes (`ClockDynamics`). Physical calibration and primitive prices remain inputs. |
| Completed carrier controls | `PMAction.ClassBlindFlip`, `PMAction.RootCliffordCompletion`, `PMAction.CompletedCarrierPhase`, `PMAction.SelectiveCarrierRouting` | Common root programs for all five internal rotations, a common odd i phase with even-sector identity, and completed Hermitian internal generators. A one-wall spatial factor is a selective neighbour route, on-site beta echo and inverse route, with exact all-state readout and original support. The selector has a root-circuit construction; admission of spatial routing on its spectral projector is a separate joint-control input. Ordinary shuffles and on-site operations cannot supply that split. Physical gate admission, clock and primitive tariffs, wall crossing and the complete walk remain open. |
| Native packet / locality | `NativePacketUpdate`, `NativePacketRouting`, `NativePacketLinks`, `NativeCoherentLinks`, `NativeLocalityBoundary`, `NativeRootGenerators` | The native E8 packet subsystem's transport/continuity contracts and finite-range boundary. Admission holds under `Admission`'s rule (`native_conserving`, `native_local`). |
| Refresh events | `RootMaintenance` | The reference-maintenance task model's swap is a root reflection on a two-carrier cell at the job's site (`encode_swap`, `event_is_root`); the minimal restoring schedule is one root event per required resource (`canonical_is_root`). |
| Repair events | `FactorRepair` | A root event acts in one non-abelian factor and the abelian phase rides on its amplitude, so a repair needs an event per displaced factor (`events_ge`) and Economy takes exactly that many (`repair_least`). On a colour and weak singlet any root event acts through its phase, so the singlet's repair is one event (`singlet_least`). Premise: a displacement in one factor is undone by one event. |
| The microscopic hop | `AxisHop`, `SliceHop`, `CarrierRootGate` | An axis step `2eⱼ` is not a root; it is a word of two roots, six of them (`axis_words_count`). Within a tick the hop is the equal-weight sum of the four in-slice words (one orbit of the slice symmetries); the other two each run the clock backwards for one event (`slice_uniform`, `clock_words_reverse`). The comparison gate's coherent step is one root reflection run for a quarter period (`root_gate_unitary`). |
| Controls from the substrate | `ConstantControls`, `ProfileControls`, `RootWordControls`, `FiniteRootWordControls`, `EdgeLocality`, `ConfigurationControls`, `D4EdgeSeparation`, `FiniteConfigurationControls` | The C² control one-forms are the gauge-field configuration (rates of the root-cost generators), and controls exist for supplied link data. Homogeneous links come from constant controls; a site-varying rate along one generator from a smooth profile; an ordered four-root pass from `RootWordControls`, and any finite ordered root program from `FiniteRootWordControls`, including repeated passes and the empty word. Slots remain inside the same middle half. `single_pass_word`, `single_pass_controls`, `four_profile` and `four_rate` recover the previous construction; `listWord_append` preserves concatenation order without commuting roots. An edge's link depends only on the controls along it, smooth Urysohn bumps glue the edges, and the middle of a `D₄` edge misses every other edge (a mixed reversal would give odd coordinate sum). So, given a finite configuration of distinct `D₄` edges with supplied finite root programs of independently varying lengths, there are C² controls whose realizations carry that data (`FiniteConfigurationControls.d4_configuration_realized`): smooth interpolation of supplied finite data, not a reconstruction of unique controls from measured links and not by itself a physical realization. |
| Continuum premises from the substrate | `NativeConsistency`, `CompactLimits` (with `PMAction.CompactTransport`) | Transports of a compactly supported C² connection are cubically consistent with it and it is `C^{1,1}`. A smooth cutoff gives the configuration's controls compact support, so the substrate's configurations meet those premises (`d4_configuration_consistent`). `ref_limit_c2`, `sum_limit_c2`: the reference-sampled limits with the links as transports, no separate consistency premise. |
| Matter in the continuum | `MatterContinuum` (with `PMAction.ScalarTransport`) | `scalar_limit_c2`: for the transports of a compactly supported C² connection and a compactly supported C² field, the event-priced scalar density converges to `Z_φ Σ_μ ‖(∂_μ + A_μ)Φ‖²` with no further premise. `spinor_hop`: a spinor hop weighted by `Γ` is `h·Γ(∂_v + A_v)Φ + O(h²)`. So the substrate's scalar and spinor fluctuations carry the continuum operators `−D²` and `γ·D` whose spectra `RunningResponse` uses. |

## Interpretation boundary
Build success certifies the conditional reversible constructions, not physical
identification. **Supplied:** banks/occupancies, amplitudes, the *payload* charge
operator, preparation of the initial reference, gate admission, clock calibration
and the price *scale*.

**Derived** E8/persistence content: carrier parity (statistics), the reference
chirality and charge (`ReferenceAnchor.reference_charges`), the clock period
(`PMSubstrate.E8Values.Delta`), the exact maintenance/supply identities, the open and infinite-domain conditions for uninterrupted
arbitrary-disturbance restoration in the retained routing
(`HomogeneousRouting.forever_iff_open`, `forever_needs_infinite`) and the minimum-execution cost
(`ReferenceMaintenance.minimum_executable_cost`).

The [boundary audit](OVERVIEW.md#reversibility-boundary) distinguishes these
updates from disposal of exported records.
-/
