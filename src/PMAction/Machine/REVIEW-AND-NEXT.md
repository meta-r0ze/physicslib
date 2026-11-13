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
  (`forever_needs_infinite`). What remains is the **prepared initial reference**:
  closed basis-preserving controls cannot supply it (`ReferenceSourceBoundary`,
  `PrimitiveRecordBoundary.cannot_prepare`, `OpenReferenceFlow`) — a preparation /
  implementation input, not a missing theorem.
- **Bank/preparation and calibration.** Physical allocation of the
  reference/record banks, clock calibration, amplitude preparation and charge
  values are supplied.
- **Native control one-forms.** The packet subsystem's two explicit inputs are the
  C² control one-forms and the admission of the coherent root-generator evolution.
  Under `Admission`'s rule the second reduces to unitarity and locality: the root
  generators are Hermitian (`NativeRootGenerators.packet_hermitian`), so `exp(−iτH)` is
  unitary; the locality statement on the packet stencil is not yet written.

No missing Lean *statement* is hidden behind these; each needs a model law or a
new construction.
