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

- **Primitive admission.** The admission *rule* is stated (`PMAction.Admission`: a
  unitary, local, priced factor is admitted unless a persistence reason excludes it),
  and the split update's directional rotations and on-site coin satisfy it
  (`direction_admitted`, `coin_admitted`). Not yet done: which E8 root words realize
  those factors (the microscopic hop, PMAction REVIEW B.2). The *overall price scale*
  is a model input (four factor applications are not four primitive events). What
  is derived: the minimum-execution cost of a supplied task
  (`ReferenceMaintenance.minimum_executable_cost`; PMConstants `TypedRepairWork`
  bounds) and the impossibility of preparing the required two-support state from
  basis-preserving gates (`PrimitiveRecordBoundary.cannot_prepare`). Admission
  (which gates) and the price scale are the inputs; the minimization is not.
- **Source contract.** The *unboundedness* is **derived, not an input**: exact
  maintenance forever holds iff the backward orbit is open
  (`HomogeneousRouting.forever_iff_open`), and a finite substrate always closes
  (`finite_closes`), so persistence forever forces an infinite substrate
  (`forever_needs_infinite`). The **prepared reference** is the vacuum:
  closed basis-preserving controls cannot supply it (`ReferenceSourceBoundary`,
  `PrimitiveRecordBoundary.cannot_prepare`), but the open line's incoming sites are vacuum,
  the unique uniform zero-cost state (`MassGap.DefectGap.cost_eq_zero_iff`), so every incoming
  site holds the same reference (`OpenReferenceFlow.vacuum_restores`). The coherent two-support
  state at the gate is one quarter-period of admitted evolution under a Hermitian involution
  (`CoherentPreparation.quarter_gate_prepares`, `quarter_gate_unitary`); `cannot_prepare`
  excludes only the basis-preserving library.
- **Bank/preparation and calibration.** Physical allocation of the
  reference/record banks, clock calibration, amplitude preparation and charge
  values are supplied.
- **Native control one-forms: longer root words.** The controls are derived for finite
  configurations whose edges each carry one ordered pass of the four root generators (see
  OVERVIEW). An edge carrying several passes needs the same staggering with more sub-intervals;
  not formalized.

No missing Lean *statement* is hidden behind these; each needs a model law or a
new construction.
