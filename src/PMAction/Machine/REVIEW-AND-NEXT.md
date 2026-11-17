# PMAction/Machine — open work (todo)

Checked constructions are in [OVERVIEW.md](OVERVIEW.md). This file is only what
remains for the machine layer. Run `./build.sh PMAction` for current counts.

## Organization backlog

- **Self-containment.** The machine's base is `PMSubstrate` only, but it still
  imports ~36 non-machine PMAction modules, 8 of them **mutual** (the target
  imports the machine back): `StateIdentification`, `CommonResponse`,
  `ChiralityConvention`, `InvolutionComparison`, `RestorationResponse`,
  `SelectedSampling`, `SubstrateReflection`, `GaugeRecordEmbedding`. The other
  ~28 are one-directional and are the shared "finite-dynamics base"
  (`FiniteEncoding`, `IsometricDynamics`, `TensorObservation/Kernel/Evolution`,
  `LocalUnitary`, `LinkConsistency`, `EventAccounting`, `Survival`,
  `Reconstruction`, `OrderComparison`, `BranchMixer*/GateBoundary/PulseContract`,
  `ExponentialLocality`, `RectangularEvolution`, `FiniteMatrixTransport`, …).
  To make the machine self-contained: extract that shared base into a
  `PMAction/Base/` layer (and resolve the 8 mutual edges). Bounded but a broad
  rename; deferred.


## Physical inputs

- Select and price the microscopic controls implementing the admitted split update. `ClassBlindFlip` and `RootCliffordCompletion` supply common root-phase circuits for all five internal generator rotations and their finite words; site-conditioned spatial transport and inter-wall crossing still need native realization and composition. Extend the single-pass construction in `RootWordControls` to edges carrying several passes.
- Specify the physical allocation of the reference and record banks, clock calibration and charge values. Amplitude preparation: the quarter-gate preparation `(1 + iH)/√2` for a Hermitian involution exists (`CoherentPreparation`); still missing is which physical input states it is applied to and how they are prepared.
