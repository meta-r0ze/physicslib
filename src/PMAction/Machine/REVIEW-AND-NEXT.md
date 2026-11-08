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

## Physical inputs (not Lean gaps)

- **Primitive admission.** The local amplitude factors / four-phase schedule are
  not yet admitted in a microscopic E8 gate library, and their prices are model
  inputs (four factor applications are not four primitive events).
- **Source contract.** A clean, indefinite record supply is an open-system input
  (`OpenReferenceFlow`); closed finite-memory persistence cannot derive it.
- **Bank/preparation and calibration.** Physical allocation of the
  reference/record banks, clock calibration, amplitude preparation and charge
  values are supplied.
- **Native control one-forms.** The packet subsystem's two explicit inputs are the
  C² control one-forms and the admission of the coherent root-generator evolution.

No missing Lean *statement* is hidden behind these; each needs a model law or a
new construction.
