# PMConstants — open work

Repo-wide named premises are listed once in [SCOPE](../../SCOPE.md#named-premises).

Checked results are in [OVERVIEW](OVERVIEW.md). `e8p` reads this library through
[`Values`](Values.lean) alone; add a name there rather than importing an internal module.

## Measured numbers that should live in e8p

Comparisons belong in `tools/e8p`. These modules still hold measured values.

- **Data that selects.** `FermionMassLaw` picks law A over law B with CMS `κ_τ = 0.92 ± 0.08`;
  its own docstring gives the substrate reason (the event law prices the squared amplitude), so
  the data step is removable, not only movable. `StrongLedgerTest` selects the integer ledger
  `L = 12` against `α_s = 0.1180 ± 0.0009`. `VevImpedance` fixes the linear form `1 + x` and the
  boundary term `χ/(Dπ)` from the data.
- **Measured numbers in conclusions.** Move the comparison and keep the conditional form:
  `ScalarSector.higgs_from_fermi` (measured `G_F` in, `125.26–125.28` GeV out), `WMassTest`,
  `VevEntry`, `VevCorrections`, `VevAccounting`, `VevBoundary`, `PlanckReadout`,
  `GravityAccounting`, `ColourChannels`, `ColourCount`, `BoundaryStorage`, `ReferenceMasses`.
- **Prose only.** About twenty further modules name measured values in docstrings
  (`Provenance`, `TableConsequences`, `RegulatoryLabels`, …). Relabel, no code change.
  `ElectroweakBounds.electronGeV` stays: it is the one declared external input.

## Premises to name or derive

- **The SU(2) and SU(3) subgroups.** `PacketGaugeActions` restricts to them; uniqueness and
  normalization are not proved. Name it in SCOPE or derive the restriction.
- **The link transport form.** `LinkMass` has the substrate picture (the scalar doublet is the
  link between the two D₄ sectors) but transports it with `θ = (g/2)W·σ + (g′/2)B` and
  hypercharge `1` put in by hand. Derive the transport or name the premise.
- **The carrier premises.** `CarrierRepresentation` rests on three: both sectors carried to the
  vector class by triality, the sign as the doublet index, and the reserved (lepton) axis. They
  are now the only inputs to the charge table (`carrierCharges_eq_standard`), so they belong in
  SCOPE.

## Naming

- **`HermitianMass` holds two unrelated things.** The superseded Hermitian-link route to `θ̄`
  (`thetaBar`, `thetaBar_eq_theta`, still used by `WallParityExchange` and
  `PMFlavor.MassMixing`) and the live vacuum weight `Z` with its cost results (`Z_zero`,
  `theta_zero_maximal`, `Z_pi`, `theta_pi_costlier`), which `ThetaBarSelection`,
  `PersistenceClosures`, `WindingWeights`, `SubstrateCharge` and `UnitTransferWitness` all use.
  Split `Z` into a module named for the vacuum weight. Ten files reference the names.

## New work this layer owes the mass chain

- **The carrier amplitude of a node-crossing displacement.** `PMAction.CompositeMass` leaves the
  three generation masses as the three carrier amplitudes
  (`CompositeMass.diag_class_independent`). The reference class crosses in-cycle; the other two
  touch the reference axis and pass the node. Derive that amplitude from the handoff price
  (`PMKAutomaton.HandoffAdmittance.closure_one_price`) with the leg count of
  `PMFlavor.NodeElimination`. Until then the generation hierarchy has one free amplitude.

## Carried over

- **Physical constant selection.** Derive the VEV correction factors, the gravitational-handoff
  interpretation, the integrated polarization remainder and the Lean verification of the
  unit-transfer history. Strong-CP selection still rests on the anomaly relation plus least-cost
  selection among candidate vacua. Blocker: no substrate rule fixes these normalizations, and the
  unit-transfer certificate is external rather than formalized.
- **Dressing outlets** (premise of `FlavourDressing`, `515/516`). The open question, whether the
  CKM loss realizes `PMFlavor.DressingEvent.event_law_spatial`, is owned by
  [PMFlavor](../PMFlavor/TODO.md); nothing to do here until it closes.
