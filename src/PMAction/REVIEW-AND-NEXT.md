# PMAction — open work

Checked results are in [OVERVIEW](OVERVIEW.md). Protocol-specific wire readouts are tracked in [PMElementaryParticles](../PMElementaryParticles/REVIEW-AND-NEXT.md).

**Physical input** marks a supplied parameter or physical identification needed by an application.
**Certificate** marks an external calculation awaiting formal verification. **Route premise** marks
a requirement of a particular derivation route. **Extension** marks a stronger result beyond the
present theorem scope. Each current theorem states the hypotheses under which its conclusion holds.

## The wire

- **Other-wall detuning (physical input).** Derive the wall-1 flip from a reference-conditioned native update and extract its `0 → 2` entry with `ReferenceDetuning.first_wall_action`. The lazy-event route needs an attempt probability and retains its derived wall-local scalar term (`NativeWallOffset`). An alternative coherent event needs a microscopic identification including its scalar term. The coherent preparation route needs both the identification of the event with the preparation and its duration in generator units. Relating either to the Wilson departure requires an independent matrix-element identity. Blocked on the protocol readout: under the readouts tested so far the data need `δ_O/k_f` from `11` to `65` across protocols, so no single derived value can be checked until the readout and channel-specific maintenance strengths are derived (PMElementaryParticles REVIEW; `CycleReadout`, `ReferenceHold`).
- **Relative crossing and carrier rates (physical input).** Derive the crossing rate relative to a lattice hop or the substrate clock and how a node admittance sets a carrier hop rate. At those derived rates, certify the light-band approximation error using `LightLeakage`; an allowed error tolerance is an accuracy criterion. A standalone isometric-map contract for the crossing would require a microscopic event identification.
- **Microscopic colour and chirality (physical input).** Derive which register carries colour, whether the crossing weights are constant on its colour orbits, and how a colour-averaged readout would be measured. The native obstruction and the independent-register construction are in the overview.
- **Physical clock and light-mode update (physical input).** Derive the substrate tick in hop-time units, establish whether the finite-tick update preserves the light subspace, and compare its restriction with the wall Hamiltonian evolution at that tick. Determine the resulting duration of one carrier event. Universal full-operator equality is settled in the overview (`SplitClockBoundary`); it cannot supply the calibration.

## Carrier update

- **Carrier spectrum and radius (certificate).** Certify the lowest positive level of the full 216-dimensional operator and the spin-up rms radius in Lean. The existing exact subspace and radius calculations are in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`.
- **Confined axial current and pion source (physical input).** Identify the confined carrier's physical axial current and pion source for the [hadron calculation](../PMHadrons/REVIEW-AND-NEXT.md). Test the many-slice wall limit or the vector–axial Ward identity at nonzero momentum transfer against the two-slice calculation in `tools/slice_axial.py`.

## Dynamics and limits

- **Even-complement realization and price (route premise).** Derive the invisible-sector action of the full physical split update, including compensation between coherent gate factors. Determine whether its admitted completions include the identity completion and whether microscopic event costs assign a positive price to invisible-mode squared displacement.
- **Polarization continuum matching (extension).** Compare the normalized primitive-period response tensor (`PrimitivePolarization`) with the continuum shell through its transverse large-volume and regulator limits. Sharpen the lattice remainder bound enough to compare it with `tools/lattice_polarization_check.py` at fixed spacing.
- **Further field limits (extension).** Establish joint-limit and operator-domain control for the integrated gauge Hessian, mode and domain control for the real-space PDE limit, the full real-space fermion field and interacting-field estimates.
