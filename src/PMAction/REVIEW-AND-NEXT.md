# PMAction — open work

Checked results are in [OVERVIEW](OVERVIEW.md). Protocol-specific wire readouts are tracked in [PMElementaryParticles](../PMElementaryParticles/REVIEW-AND-NEXT.md).

## The wire

- **Other-wall detuning.** Derive the wall-1 flip from a reference-conditioned native update and extract its `0 → 2` entry with `ReferenceDetuning.first_wall_action`. The lazy-event route needs an attempt probability. The coherent preparation route needs both the identification of the event with the preparation and its duration in generator units. Relating either to the Wilson departure requires an independent matrix-element identity. Blocked on the protocol readout: under the readouts tested so far the data need `δ_O/k_f` from `11` to `65` across protocols, so no single derived value can be checked until the readout works (PMElementaryParticles REVIEW; `CycleReadout`, `ReferenceHold`).
- **Wall-local phase.** Determine which event the native wall performs, including its scalar phase, to choose between the lazy and coherent mass laws in `WallOffset`.
- **Crossing and carrier rates.** Derive whether the bare crossing preserves norm, how a node admittance sets a carrier hop rate, and what physical leakage bound limits the vector rate.
- **Microscopic colour and chirality.** Derive which register carries colour, whether the crossing weights are constant on its colour orbits, and how a colour-averaged readout would be measured. The native obstruction and the independent-register construction are in the overview.
- **Physical update and clock.** Identify the finite-tick update on the light wall modes and its duration in hop-time units. Test whether it equals the exponential of the wall Hamiltonian at the substrate clock. A light-mode update that does not commute with the Hamiltonian would rule out that identification.

## Carrier update

- Certify the lowest positive level of the full 216-dimensional operator and the spin-up rms radius in Lean. The existing exact subspace and radius calculations are in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`.
- Identify the confined carrier's physical axial current and pion source for the [hadron calculation](../PMHadrons/REVIEW-AND-NEXT.md). Test the many-slice wall limit or the vector–axial Ward identity at nonzero momentum transfer against the two-slice calculation in `tools/slice_axial.py`.

## Dynamics and limits

- **Even complement.** Determine whether coherent gate sequences implement the identity completion of the physical split update, including its directional factors at the actual tick. Derive whether the microscopic event ledger charges invisible-mode squared displacement at a positive rate. The permutation-gate classification and the five-site directional locality obstruction are in the overview.
- **Lattice polarization.** Replace the continuum shell by a Brillouin-zone sum, prove the wrap identities for `PolarizationContact.finite_routing_cancel`, and handle zero modes compatibly with the shift. Sharpen the lattice remainder bound enough to compare it with `tools/lattice_polarization_check.py` at fixed spacing.
- Establish shared group and trace normalization across spacings.
- Establish mode and domain control for the real-space PDE limit, the integrated Hessian, the full real-space fermion field and interacting-field estimates.
