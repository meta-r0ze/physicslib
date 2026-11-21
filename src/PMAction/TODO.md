# PMAction — open work

Checked results are in [OVERVIEW](OVERVIEW.md). The shared clock, record and
handoff tasks are in the [transport review](../PMKAutomaton/TODO.md).

**Extension** marks a stronger result beyond the present theorem scope. **Certificate** marks an
external calculation awaiting formal verification. Each current theorem states its hypotheses.

## Substrate premises

None open.

The protocol register (which E8 structure carries protocol identity) is Paper III's application, not
a PMAction premise: PMAction supplies the constraints (`ColourRegister`: colour is a separate factor,
not the carrier axes), the factor construction (`IndependentRegisters`) and the stationary even sector
(`EvenComplement`). It is tracked in PMElementaryParticles REVIEW.

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
