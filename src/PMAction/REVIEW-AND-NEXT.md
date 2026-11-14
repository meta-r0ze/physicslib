# PMAction — open work

## Carrier update

- Certify the lowest positive carrier level on the full 216-dimensional operator, then certify the spin-up rms radius in Lean. The exact subspace calculation is in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`; the full-space level ordering still uses floating point.
- Find the physical axial current of the carrier. The two-slice update's own local axial rotation is the slice sign: it commutes with every hop and the on-site term and is broken only by the inter-slice coupling, and its link current `sym(S v_j)` is exactly normalized for free carriers (`tools/slice_axial.py`). On the confined carrier it gives `0.22–0.45` (`n = 3…8`) against the on-site `Σ_z` `0.83–0.67`, extrapolating to about `0.5` against `0.65`: with two slices the wall leakage is `O(1)`, so this current neither confirms the on-site operator nor gives a usable `g_A`. Next candidates: the many-slice limit of the wall, or the vector-axial Ward identity at nonzero momentum transfer. The [hadron calculation](../PMHadrons/REVIEW-AND-NEXT.md) needs this current and pion source.

## Dynamics and limits

- Construct the map from background `Config` to the `RecordSupply` stream used by `ReferenceSelection`. Physical allocation of the banks is a [machine-layer dependency](Machine/REVIEW-AND-NEXT.md).
- Establish shared group and trace normalization across spacings. Multi-pass root words are tracked in the machine review.
- Identify the directional-exponential completion with the on-site completion, or specify the conditions for their agreement.
- Establish mode and domain control for the real-space PDE limit, the integrated Hessian, the full real-space fermion field and interacting-field estimates.
- The phase of a node-crossing hop. `WallHopPhase` shows in-wall spatial hops carry a quarter turn
  that cancels in every reduced coupling, so the CKM flux (`PMFlavor/REVIEW-AND-NEXT.md`, about
  `49°`) must come from elsewhere. The node crossings are spinor-class displacements with a
  time-axis component `±1` (`PMFlavor.ExchangeAxis.spinor_touch`), which is not a spatial `αⱼ`
  hop. Compute the amplitude of such a displacement on one chirality, in the discrete-time update
  (the time component is a tick, not a hopping term), and its phase relative to the in-wall legs.
  Also state the lead model (equal leads per generation) here as a premise, since
  `PMFlavor.TransferGenerator` uses it.
- A direct zero-mode mass term. The flavour sector (`PMFlavor.MassInsertion`,
  `InterWallDiagonal`) excludes the charged masses as `δ²Y⁻¹` or `D Y⁻¹ D` with the equal-class
  link the E₈ gluing allows: traceless, or a degenerate light pair. What it needs is a term
  joining wall 1's `Γ = +1` zero mode to wall 2's `Γ = −1` zero mode directly, carrying the
  generation's label class (class gap `b + c`). The two-wall Hamiltonian here has only the on-site
  `δβ` (within a wall) and the inter-wall hop `hop ⊗ Y`, which joins the gapped components. Ask:
  does the E₈ update contain a direct zero-mode term (a crossing combined with a label-class
  carrier in one event)? And why is the equal-class crossing, which the gluing allows directly,
  absent or small in the mass? If it is not small it puts generation off-diagonal entries back
  into the mass matrix.

