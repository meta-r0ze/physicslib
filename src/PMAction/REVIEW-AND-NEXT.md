# PMAction — open work

Checked results are in [OVERVIEW](OVERVIEW.md). Protocol-specific wire readouts are tracked in [PMElementaryParticles](../PMElementaryParticles/REVIEW-AND-NEXT.md).

## The wire

- **Other-wall detuning.** Derive the wall-1 flip from a reference-conditioned native update and extract its `0 → 2` entry with `ReferenceDetuning.first_wall_action`. The lazy-event route needs an attempt probability and retains its derived wall-local scalar term (`NativeWallOffset`). An alternative coherent event needs a microscopic identification including its scalar term. The coherent preparation route needs both the identification of the event with the preparation and its duration in generator units. Relating either to the Wilson departure requires an independent matrix-element identity. Blocked on the protocol readout: under the readouts tested so far the data need `δ_O/k_f` from `11` to `65` across protocols, so no single derived value can be checked until the readout and channel-specific maintenance strengths are derived (PMElementaryParticles REVIEW; `CycleReadout`, `ReferenceHold`).
- **Relative crossing and carrier rates.** Derive the crossing rate relative to a lattice hop or the substrate clock, how a node admittance sets a carrier hop rate, and what physical leakage bound limits the vector rate. A standalone isometric-map contract for the crossing would require a microscopic event identification.
- **Microscopic colour and chirality.** Derive which register carries colour, whether the crossing weights are constant on its colour orbits, and how a colour-averaged readout would be measured. The native obstruction and the independent-register construction are in the overview.
- **Physical clock and light-mode update.** Derive the substrate tick in hop-time units, establish whether the finite-tick update preserves the light subspace, and compare its restriction with the wall Hamiltonian evolution at that tick. Determine the resulting duration of one carrier event. Universal full-operator equality is settled in the overview (`SplitClockBoundary`); it cannot supply the calibration.

## Carrier update

- Certify the lowest positive level of the full 216-dimensional operator and the spin-up rms radius in Lean. The existing exact subspace and radius calculations are in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`.
- Identify the confined carrier's physical axial current and pion source for the [hadron calculation](../PMHadrons/REVIEW-AND-NEXT.md). Test the many-slice wall limit or the vector–axial Ward identity at nonzero momentum transfer against the two-slice calculation in `tools/slice_axial.py`.

## Dynamics and limits

- **Even complement.** Determine whether coherent gate sequences implement the identity completion of the physical split update, including its directional factors at the actual tick. Derive whether the microscopic event ledger charges invisible-mode squared displacement at a positive rate. The permutation-gate classification and the five-site directional locality obstruction are in the overview.
- **Polarization normalization and continuum matching.** Fix the physical volume and momentum-measure normalization of the finite D₄ response tensor, and compare its transverse large-volume and regulator limits with the continuum shell. Sharpen the lattice remainder bound enough to compare it with `tools/lattice_polarization_check.py` at fixed spacing.
- Establish shared group and trace normalization across spacings.
- Establish mode and domain control for the real-space PDE limit, the integrated Hessian, the full real-space fermion field and interacting-field estimates.
