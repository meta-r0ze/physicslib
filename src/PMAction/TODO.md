# PMAction — open work

Repo-wide named premises are listed once in [SCOPE](../../SCOPE.md#named-premises).

Checked results are in [OVERVIEW](OVERVIEW.md). The shared clock, record and
handoff tasks are in the [transport review](../PMKAutomaton/TODO.md).

**Extension** marks a stronger result beyond the present theorem scope. **Certificate** marks an
external calculation awaiting formal verification. Each current theorem states its hypotheses.

## Scope premises

- **Spacetime and amplitude structure.** Derive the Lorentzian signature and complex amplitude from
  substrate persistence instead of entering them as modelling premises; the finite gauge measure has
  site-reflection positivity. Blocker: no selection principle fixes the signature or complex structure,
  and the MassGap branch covers only the distinction substrate, not a continuum relativistic gauge
  theory (see [MassGap/README.md](MassGap/README.md)).

## Extensions

- **Polarization continuum matching.** Compare the normalized primitive-period response tensor
  (`PrimitivePolarization`) with the continuum shell through its transverse large-volume and regulator
  limits. Sharpen the lattice remainder bound enough to compare it with
  `tools/lattice_polarization_check.py` at fixed spacing.
- **Further field limits.** Establish joint-limit and operator-domain control for the integrated gauge
  Hessian, mode and domain control for the real-space PDE limit, the full real-space fermion field and
  interacting-field estimates.

## Certificates

- **Carrier spectrum and radius.** Certify the lowest positive level of the full 216-dimensional
  operator and the spin-up rms radius in Lean. The existing exact subspace and radius calculations are
  in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`.

## Generation masses

The generation-mass modules (`MassInsertion`, `GenerationMass`, `GenerationSector`,
`GenerationOrientation`, `InterWallDiagonal`) point here.

- **Reconcile the two levels of the wall crossing.** `WallTransfer` (Conservation) makes the
  equal-class crossing the mass bilinear, the only term joining the walls. `DomainWall` and
  `WallSeesaw` put the same crossing on the gapped components, so masses come only through the
  seesaw `δ² Y⁻¹`. The two give opposite patterns (`tools/generation_mass_levels.py`): the
  carrier level gives one heavy and two light generations (the class amplitudes, `1 : 1 : α⁻¹`);
  the seesaw gives one light and two heavy, for a flavour-blind detuning and for a label
  insertion. `MassInsertion`'s CKM ordering also excludes the seesaw. Restate the domain-wall
  Hamiltonian so the crossing acts on the chiral zero modes, or show why it cannot.
- **Node factor of a mass.** At the carrier level the masses are the crossing amplitudes: the
  reference class in-cycle (`1`), the spinor classes through the node. Two legs for colour
  carriers (`PMFlavor.NodeElimination`) give `α`, so heavy/light `= α⁻¹ ≈ 137`. Lepton-axis
  carriers are one leg from the node (`√α`). Open: the down-type and lepton sectors (the leg rule
  alone gives `α⁻¹` and `α^{−1/2}`), and what splits the two light generations (degenerate at
  this order). Comparisons belong in e8p.
- **Single crossing at a fixed class.** Whether `GenerationOrientation.single_crossing_unequal`
  is a physical move.

