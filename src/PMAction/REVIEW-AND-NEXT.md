# PMAction — open work

## Generation sector

The six-step plan is done (results in [OVERVIEW](OVERVIEW.md), `GenerationSector`). Open:

- **Node amplitude.** The amplitude with which the reference node supplies a spinor-class carrier,
  in the units of the vector-class edge. It sets both the heavy/light mass ratio (the composite of
  `PMConstants.GenerationMass`) and the suppression of `|V_ub|`, `|V_cb|`
  (`PMConstants.GenerationWeak`), so one value must fit both. The two-leg/one-leg rule
  (`PMFlavor.NodeElimination`) does not fit the masses; do not tune it.
- **Light-pair split.** Reduced to the carriers. `ReferenceDetuning` gives `δ = 0` on the reference's
  wall (premise: the reference is a stationary zero mode of the same update), so
  `PMFlavor.ReferenceWallMass` factors `M = D_R (δ_O + cyc κ_O)` and the light ratio is
  `κ_R(s)/κ_O(s)`, one spinor-class carrier on versus off the reference's wall. Node passage acts on
  both walls (`PMFlavor.LeptonAxisRestriction`); the difference must come from the repair, whose weak
  sign exchange acts on the left sector only (`weak_type`). Derive the node-passage cost on each
  wall; the same numbers fix the node amplitude item above.

## Carrier update

- Certify the lowest positive carrier level on the full 216-dimensional operator, then certify the spin-up rms radius in Lean. The exact subspace calculation is in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`; the full-space level ordering still uses floating point.
- Find the physical axial current of the carrier. The two-slice update's own local axial rotation is the slice sign: it commutes with every hop and the on-site term and is broken only by the inter-slice coupling, and its link current `sym(S v_j)` is exactly normalized for free carriers (`tools/slice_axial.py`). On the confined carrier it gives `0.22–0.45` (`n = 3…8`) against the on-site `Σ_z` `0.83–0.67`, extrapolating to about `0.5` against `0.65`: with two slices the wall leakage is `O(1)`, so this current neither confirms the on-site operator nor gives a usable `g_A`. Next candidates: the many-slice limit of the wall, or the vector-axial Ward identity at nonzero momentum transfer. The [hadron calculation](../PMHadrons/REVIEW-AND-NEXT.md) needs this current and pion source.

## Dynamics and limits

- **Subtracted lattice polarization** (unblocks `PMConstants` running couplings). The missing link
  is a theorem about the same subtracted observable on the lattice that `PMConstants` can consume.
  (a) The finite-`q` vertex. Done in part (`FiniteVertex`): the Ward identity is exact
  (`ward`), and the conserved vertex is the midpoint vertex with each root weighted by
  `sin x / x`, `x = a r·q/2`; the midpoint vertex alone misses it by `O(a²|k||q|³)`
  (`midpoint_gap`). Still open: the two-field contact (seagull) term of the gauged hop, and the
  transversality of the lattice `Π_μν` it should restore. (b) Bound lattice minus continuum after
  subtracting the `q = 0` value, on the shell of `PolarizationRemainder.polarization_window`, with
  `symbol_gap` at both `k` and `k + q` and the weighted vertex. Acceptance: the bound must resolve
  the `q²` coefficient. An `O(a²)` estimate independent of `q` proves convergence at fixed `q` but
  is useless after division by `q²`. Whether the existing estimates are sharp enough after the
  subtraction is open.
- **Inertia certificate** (unblocks `PMConstants` strong CP: the unit-winding witness). One reusable
  theorem beside `InertiaStability`, mirroring `tools/unit_transfer_certificate.py`: for Hermitian
  `H`, a proposed basis `Q` and `B = Qᴴ H Q`,
  (a) `‖Qᴴ Q − 1‖ < 1` makes `Q` invertible;
  (b) if every row's off-diagonal sum of `B` is below its `|diagonal|`, the path
  `diag B + t · offdiag B`, `t ∈ [0, 1]`, stays invertible (Gershgorin,
  `Matrix.det_ne_zero_of_sum_row_lt_diag`), so by `negCount_locallyConstant` the negative count of
  `B` is the number of negative diagonal entries;
  (c) Sylvester's law of inertia: `negCount (Qᴴ H Q) = negCount H` for invertible `Q` (not in the
  library; `count_le` has the needed form estimates).
  Then the certificate checks only inequalities and signs, not a dense eigensolve. Still required:
  a checked correspondence between the certificate's matrices and the library's two Wilson
  backgrounds. The physical premise that the vacuum selects among the weighted phases stays
  explicit (`ThetaBarSelection`).

- Construct the map from background `Config` to the `RecordSupply` stream used by `ReferenceSelection`. Physical allocation of the banks is a [machine-layer dependency](Machine/REVIEW-AND-NEXT.md).
- Establish shared group and trace normalization across spacings. Multi-pass root words are tracked in the machine review.
- Identify the directional-exponential completion with the on-site completion, or specify the conditions for their agreement.
- Establish mode and domain control for the real-space PDE limit, the integrated Hessian, the full real-space fermion field and interacting-field estimates.
- Mass terms of the two-wall Hamiltonian. (1) A direct light-mode term: `ZeroModeCoupling` locates
  it as the off-Wilson part of the inter-sector hop, `(r − 1)·βx`; the wall at `r = 1` has none, and
  no source of `r ≠ 1` (or another direct term) is identified. (2) The inter-wall link `Y_gap`: decided, one-directional within a convention
  (`PMConstants.GenerationParity`), equal seesaw masses (`PMFlavor.CyclicSeesaw`). The hierarchy is
  the composite of `PMConstants.GenerationMass` (crossing then label-class carrier), a
  second-order, generation-diagonal term. It enters as a correction to `δ`
  (`PMFlavor.CompositeMass`: `M = D₂ Y⁻¹ D₁ᴴ`, and a carrier with the crossing's support turns `Y⁻¹`
  diagonal). The carrier's chirality-flip part is the Wilson part of the hop, `−(r/2)β`, the
  on-site mass operator (`CarrierFlip`), provided the class carrier is an in-wall Wilson hop. (3) Bound the seesaw
  contribution against any direct term (else generation off-diagonal mass entries return).
- Lead coupling (if pursued): a microscopic derivation of how the generations couple to the leads of
  the charged-current transfer. The equal-width assumption itself is a flavour-model premise owned
  by `PMFlavor.TransferGenerator`.
