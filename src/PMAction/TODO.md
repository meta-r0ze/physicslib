# PMAction — open work

Repo-wide named premises are listed once in [SCOPE](../../SCOPE.md#named-premises).

Checked results are in [OVERVIEW](OVERVIEW.md). The shared clock, record and
handoff tasks are in the [transport review](../PMKAutomaton/TODO.md).

**Extension** marks a stronger result beyond the present theorem scope. **Certificate** marks an
external calculation awaiting formal verification. Each current theorem states its hypotheses.

## Scope premises

- **Wall and wire inputs.** Derive the detuning, carrier transfers and paid
  flag schedule that enter `DetunedWire.detunedWireOperator` and
  `TollAmplitude.weightedFlagCost` for a specific persistent configuration.

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

## Occupied program accounting

`CommonResponse.bookedCapacity` adds capacity times registration weight over a supplied visit set. The physical resources, local valuations and visits still need to come from a complete recurring execution. The [EP occupancy-cost TODO](../PMElementaryParticles/TODO.md#occupancy-cost) tracks that construction.

- **Single crossing at a fixed class.** Whether `GenerationOrientation.single_crossing_unequal`
  is a physical move.
