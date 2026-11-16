# PMAction — open work

Checked results are in [OVERVIEW](OVERVIEW.md). Protocol-specific wire readouts are tracked in [PMElementaryParticles](../PMElementaryParticles/REVIEW-AND-NEXT.md).

**Substrate premise** marks a supplied parameter or identification still to derive from the E8 update. **Certificate** marks an external calculation awaiting formal verification. **Route premise** marks a requirement of a particular derivation route. **Extension** marks a stronger result beyond the present theorem scope. Each current theorem states its hypotheses. Derive the substrate protocol first; comparisons with observed particles test the result rather than choose it.

The immediate ElementaryParticles dependency is the event clock below. When dependencies are equal, close admission and pricing premises before extending the wire analysis. The carrier level and radius are later certification work.

## Substrate premises

- **Event clock: crossing, carrier and flip rates (substrate premise).** Derive the duration of one native event in hop-time units and the substrate tick, then the wall-crossing rate `y` and the in-wall carrier and flip rates in those units (a certain event of duration `τ` has rate `≥ π/(2τ)`, `CertainTransferRate`; how a node admittance becomes a Hamiltonian rate needs the same duration). `WallGapCalibration`: the native realization, glue support and stationary reference alone admit every flip-to-crossing ratio, so a microscopic relation is needed. `SplitClockBoundary` excludes identifying the split update with one Hamiltonian exponential; compare the finite-tick update with the wall evolution on the light subspace instead. At the derived rates, certify the light-band error with `LightLeakage` (the first-row deficit depends on it).
- **Lazy or coherent flip event (substrate premise).** Economy fixes the other wall's flip on a root of `δ³ = −κ_O0κ_O1κ_O2` (`OtherWallStationary`). As the library's lazy `β` event it is the real root, realized by attempt probability `(1 − e^{−|δ|})/2` (`OtherWallFlipEvent`), but it leaves a wall-local offset that turns the light masses into `s²/c'` (`WallOffset`); as a coherent event it keeps the singular values `s` but needs its identification and duration. Derive which the native event is (the same clock question as above).
- **Even-complement realization and price (route premise).** Derive the invisible-sector action of the full physical split update, including compensation between coherent gate factors. Determine whether its admitted completions include the identity completion and whether microscopic event costs assign a positive price to invisible-mode squared displacement.
- **Microscopic colour and chirality (substrate premise).** Derive which register carries colour, whether the crossing weights are constant on its colour orbits, and how a colour-averaged readout would be measured. The native obstruction and the independent-register construction are in the overview.
- **Confined axial current and pion source (substrate premise).** Identify the confined carrier's axial current and pion source for the [hadron calculation](../PMHadrons/REVIEW-AND-NEXT.md). Test the many-slice wall limit or the vector–axial Ward identity at nonzero momentum transfer against the two-slice calculation in `tools/slice_axial.py`.

## Extensions

- **Polarization continuum matching (extension).** Compare the normalized primitive-period response tensor (`PrimitivePolarization`) with the continuum shell through its transverse large-volume and regulator limits. Sharpen the lattice remainder bound enough to compare it with `tools/lattice_polarization_check.py` at fixed spacing.
- **Further field limits (extension).** Establish joint-limit and operator-domain control for the integrated gauge Hessian, mode and domain control for the real-space PDE limit, the full real-space fermion field and interacting-field estimates.

## Certificates

- **Carrier spectrum and radius (certificate).** Certify the lowest positive level of the full 216-dimensional operator and the spin-up rms radius in Lean. The existing exact subspace and radius calculations are in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`.
