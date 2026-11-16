# PMAction — open work

Checked results are in [OVERVIEW](OVERVIEW.md). Protocol-specific wire readouts are tracked in [PMElementaryParticles](../PMElementaryParticles/REVIEW-AND-NEXT.md).

**Substrate premise** marks a supplied parameter or identification still to derive from the E8 update. **Certificate** marks an external calculation awaiting formal verification. **Route premise** marks a requirement of a particular derivation route. **Extension** marks a stronger result beyond the present theorem scope. Each current theorem states its hypotheses. Derive the substrate protocol first; comparisons with observed particles test the result rather than choose it.

The immediate ElementaryParticles dependencies are the crossing-to-flip calibration, followed by the native-current/external-state bridge to `AmplitudeTrace`. When dependencies are equal, close admission and pricing premises before extending the wire analysis. The carrier level and radius are later certification work.

## Immediate handoff

- **Relative crossing and carrier rates (substrate premise).** Derive the wall-crossing rate `y` and in-wall flip/carrier rates from native event histories in the same clock units. Derive how a node admittance sets a Hamiltonian hop rate, including event duration or the generator/update relation. `WallGapCalibration` proves that the supplied native-wall realization, cyclic glue support and stationary reference alone admit every positive flip-to-crossing ratio; a further microscopic relation is needed. `WallMassRatio` supplies a conditional capacity-to-mass identification in an equal-detuning model, not that missing relation for the reference-conditioned wire. At the derived rates, certify the light-band approximation error using `LightLeakage`. A standalone isometric-map contract for the crossing would also require a microscopic event identification.
- **Native current to external amplitude (substrate premise).** Construct the prepared native external modes, their charged-current matrix elements, final-channel selection and normalization, and connect them to `AmplitudeTrace`. Its trace algebra and `WeakVertex`'s contact-limit and kernel-basis results are already proved. `WallCurrentWeights` identifies the charged gapped component retained by the full projector: total gapped weight alone is not a protocol row deficit. Derive the appropriate state/channel identity before using a leakage fraction as a readout. Protocol-specific applications belong in ElementaryParticles.

## Other substrate and route premises

- **Even-complement realization and price (route premise).** Derive the invisible-sector action of the full physical split update, including compensation between coherent gate factors. Determine whether its admitted completions include the identity completion and whether microscopic event costs assign a positive price to invisible-mode squared displacement.
- **Other-wall detuning (substrate premise).** `OtherWallStationary`: if the other wall carries a stationary light state as the reference wall does, its flip is a root of `δ³ = −κ_O0κ_O1κ_O2` and the stationary state occupies every label; PMElementaryParticles finds every protocol's fit within a few percent of the real root. Derive that each wall carries a stationary light state from the update (the premise above), and the microscopic event that realizes the flip at that value (lazy event: attempt probability with its wall-local scalar term, `NativeWallOffset`; coherent event: its identification and duration in generator units), with its `0 → 2` entry from `ReferenceDetuning.first_wall_action`.
- **Microscopic colour and chirality (substrate premise).** Derive which register carries colour, whether the crossing weights are constant on its colour orbits, and how a colour-averaged readout would be measured. The native obstruction and the independent-register construction are in the overview.
- **Substrate clock and light-mode update (substrate premise).** Derive the substrate tick in hop-time units, establish whether the finite-tick update preserves the light subspace, and compare its restriction with the wall Hamiltonian evolution at that tick. Determine the resulting duration of one carrier event. Universal full-operator equality is settled in the overview (`SplitClockBoundary`); it cannot supply the calibration.
- **Confined axial current and pion source (substrate premise).** Identify the confined carrier's axial current and pion source for the [hadron calculation](../PMHadrons/REVIEW-AND-NEXT.md). Test the many-slice wall limit or the vector–axial Ward identity at nonzero momentum transfer against the two-slice calculation in `tools/slice_axial.py`.

## Extensions

- **Polarization continuum matching (extension).** Compare the normalized primitive-period response tensor (`PrimitivePolarization`) with the continuum shell through its transverse large-volume and regulator limits. Sharpen the lattice remainder bound enough to compare it with `tools/lattice_polarization_check.py` at fixed spacing.
- **Further field limits (extension).** Establish joint-limit and operator-domain control for the integrated gauge Hessian, mode and domain control for the real-space PDE limit, the full real-space fermion field and interacting-field estimates.

## Certificates

- **Carrier spectrum and radius (certificate).** Certify the lowest positive level of the full 216-dimensional operator and the spin-up rms radius in Lean. The existing exact subspace and radius calculations are in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`.
