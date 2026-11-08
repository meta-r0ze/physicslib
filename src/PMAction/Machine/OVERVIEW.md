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
| Native packet / locality | `NativePacketUpdate`, `NativePacketRouting`, `NativePacketLinks`, `NativeCoherentLinks`, `NativeLocalityBoundary`, `NativeRootGenerators` | The native E8 packet subsystem's transport/continuity contracts and finite-range boundary. The C² control one-forms and admission remain inputs. |

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
