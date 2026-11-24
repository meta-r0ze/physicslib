# PMConstants — open work

Repo-wide named premises are listed once in [SCOPE](../../SCOPE.md#named-premises).

Checked results are in [OVERVIEW](OVERVIEW.md). `e8p` reads this library through
[`Values`](Values.lean) alone; add a name there rather than importing an internal module.

## Measured numbers that should live in e8p

Comparisons belong in `tools/e8p`. These modules still hold measured values.

- **Data that selects.** Three done: the fermion mass law (the event law and Economy each select
  law A, `κ_τ` comparisons in e8p); the strong ledger (`ColourChannels.colour_ledger` derives
  `L₃ = 12η` from the colour-bulk channel count; the `α_s` comparison and the window are in e8p);
  and the VEV's linear correction form (`VevReadout.exact_net_is_identity` and `residual_series`
  derive `1 + x` from exact repair; the `exp` and geometric window comparisons are in e8p).
  Still open: the rest of `VevCorrections` and `VevReadout` state their results against the Fermi
  window itself (`divisor_window`, `dimension_window`, `boundary_unique`,
  `bare_dimension_excluded`, `qed_like_excluded`, `compound_excluded`, `total_excluded`). The
  derivations they test now exist (`VevBoundary` for `χ/(Dπ)`, `VevNoise.noise_share` and
  `VevReadout.normalized_share` for the divisor), so the whole group moves in one pass: keep the
  derived form here, put every window statement in e8p.
- **Measured numbers in conclusions.** Move the comparison and keep the conditional form:
  `ScalarSector.higgs_from_fermi` (measured `G_F` in, `125.26–125.28` GeV out), `WMassTest`,
  `VevEntry`, `VevAccounting`, `VevBoundary`, `PlanckReadout`,
  `GravityAccounting`, `BoundaryStorage`, `ReferenceMasses`.
- **Prose only.** About twenty further modules name measured values in docstrings
  (`Provenance`, `TableConsequences`, `RegulatoryLabels`, …). Relabel, no code change.
  `ElectroweakBounds.electronGeV` stays: it is the one declared external input.

## Premises to name or derive

- **The weak `SU(2)` on the sign pair.** Two thirds of the old subgroup premise are now derived in
  `ReferenceAxis`: colour is the stabilizer of the reference axis (`axis_stabilizer`, already
  there), and `bl` is the only axis charge that commutes with colour, is traceless and reads `−1`
  on that axis (`bl_unique`, new, with `diagonal_commutant`). What is left is the weak factor: the
  sign flip is the only move between the two carriers on an axis
  (`CarrierActions.same_axis_iff`), but that the action on the pair is the continuous `SU(2)` is
  not proved. Named in SCOPE.
- **The link transport form.** `LinkMass` has the substrate picture (the scalar doublet is the
  link between the two D₄ sectors) and the link's unit charge is now derived
  (`link_charge_one`, `thetaY_one`, from `CarrierRepresentation.carrierCharges_yukawa`). The
  transport `θ = (g/2)W·σ + (g′/2)Y B` itself is still put in by hand. The route: the link is
  transported by the packet actions restricted to it, and `link_quadratic` is already the
  second-order form of the event law's price, so this closes once the weak factor above does.
- **Stiffness per unit of conserved charge.** `GeneratorNormalization` selects charge units over
  the packet trace form and names the one step left: a derivation, from the event law, that
  refresh stiffness is counted per unit of conserved charge. That is the `(g/2)`, `(g′/2)`
  normalization, and it belongs next to `PMAction.CommonResponse`/`LinkFromEvents`.
- **The carrier premises.** `CarrierRepresentation` rests on three: both sectors carried to the
  vector class by triality, the sign as the doublet index, and the reserved (lepton) axis. They
  are the only inputs to the charge table (`carrierCharges_eq_standard`) and, through
  `ReferenceAxis`, to the colour subgroup and hypercharge generator of the packet action as well.
  Named in SCOPE. The concentration of load on the reserved-axis premise is now this layer's main
  single risk: it carries every charge in the tower and the colour subgroup, and nothing else
  would catch it being wrong.

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
