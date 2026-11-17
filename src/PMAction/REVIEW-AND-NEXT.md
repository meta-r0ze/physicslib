# PMAction — open work

Checked results are in [OVERVIEW](OVERVIEW.md). Machine-layer organization is in
[Machine/REVIEW-AND-NEXT.md](Machine/REVIEW-AND-NEXT.md).

**Extension** marks a stronger result beyond the present theorem scope. **Certificate** marks an
external calculation awaiting formal verification. Each current theorem states its hypotheses.

## Substrate premises

None open.

The protocol register (which E8 structure carries protocol identity) is Paper III's application, not
a PMAction premise: PMAction supplies the constraints (`ColourRegister`: colour is a separate factor,
not the carrier axes), the factor construction (`IndependentRegisters`) and the stationary even sector
(`EvenComplement`). It is tracked in PMElementaryParticles REVIEW.

## Extensions

- **Absolute event clock.** Durations of the native events in hop-time units and their relation to
  the substrate tick: the crossing rate `y`, the in-wall carrier and flip rates, and the timing and
  price of the native control circuits (`ClassBlindFlip`, `RootCliffordCompletion`,
  `CompletedCarrierPhase`, `SelectiveCarrierRouting`). Downstream ratios do not use it: the light-mass
  ratios and the routing are set by `k/K`, the resonance and the reference. It is needed for absolute
  scales, for converting node admittances into Hamiltonian rates (`CertainTransferRate`), for the
  light-band error at derived rates (`LightLeakage`; `WallGapCalibration` leaves the flip-to-crossing
  ratio free), and for the finite-tick walk (`SplitClockBoundary` excludes a single Hamiltonian
  exponential). The ratios need less than the absolute clock: for certain events a rate ratio is a
  duration ratio (`CertainTransferRate`), so the root attempt rate `p` cancels, and the flip program is
  `32` root quarter-times (`ClassBlindFlip.forwardTimes_total`). The flip-to-crossing ratio, which the
  light-band leakage and EP's first-row deficit need, then waits only on the crossing's root program,
  which the library does not yet construct. As E8 reflections, moving a carrier between the
  generation's two wall classes takes three (`tools/event_clock_check.py`; one for equal classes);
  whether the flip program is minimal is open. The absolute clock is `p` (`Machine/RootTransferPhase`:
  quarter-time `π/(2 gap p)` ticks).
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
