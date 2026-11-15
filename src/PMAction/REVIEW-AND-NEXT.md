# PMAction — open work

## Generation sector

The six-step plan is done, and the wire's mass form is derived (OVERVIEW: `GenerationSector`,
`CarrierFlip`, `ReferenceDetuning`; `PMFlavor.ReferenceWallMass`: `M = D_R (δ_O + cyc κ_O)`). How
each species uses the wire is protocol work in
[PMElementaryParticles](../PMElementaryParticles/REVIEW-AND-NEXT.md). The node amplitude is
derived (`PMFlavor.NodeAmplitude`: `k/K = α/2`). Open, wire only:

- **Size of the other wall's detuning.** `ReferenceDetuning` puts the reference's wall at the
  Wilson point (`δ_R = 0`), so the seesaw term `δ_F δ_T Y⁻¹` vanishes and the light mass is
  `D_R (δ_O + cyc κ_O)` with no competing direct term on the reference's wall. The other wall's
  detuning `δ_O` (in `ZeroModeCoupling`'s terms, its departure from `r = 1`) sets the mass scale and,
  relative to the carriers, the mixing. It must be nonzero: at `δ_O = 0` the mass is a cyclic shift
  with masses `(kK, k², kK)`, two heavy and one light (`PMFlavor.UndetunedWall`), the reverse of
  every charged sector. Find what fixes its size on the substrate; the library has no source yet
  (the wire's simplest protocol, down quarks, puts it near `0.025 K`, an external fit,
  `tools/node_carrier_scan.py`).

## Carrier update

- Certify the lowest positive carrier level on the full 216-dimensional operator, then certify the spin-up rms radius in Lean. The exact subspace calculation is in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`; the full-space level ordering still uses floating point.
- Find the physical axial current of the carrier. The two-slice update's own local axial rotation is the slice sign: it commutes with every hop and the on-site term and is broken only by the inter-slice coupling, and its link current `sym(S v_j)` is exactly normalized for free carriers (`tools/slice_axial.py`). On the confined carrier it gives `0.22–0.45` (`n = 3…8`) against the on-site `Σ_z` `0.83–0.67`, extrapolating to about `0.5` against `0.65`: with two slices the wall leakage is `O(1)`, so this current neither confirms the on-site operator nor gives a usable `g_A`. Next candidates: the many-slice limit of the wall, or the vector-axial Ward identity at nonzero momentum transfer. The [hadron calculation](../PMHadrons/REVIEW-AND-NEXT.md) needs this current and pion source.

## Dynamics and limits

- **Subtracted lattice polarization** (unblocks `PMConstants` running couplings). The vertex
  bookkeeping is done (OVERVIEW: `FiniteVertex`, `PolarizationContact`). Open: bound lattice minus
  continuum after subtracting the `q = 0` value, on the shell of
  `PolarizationRemainder.polarization_window`, with `symbol_gap` at both `k` and `k + q`, the
  sinc-weighted vertex and the contact term; on a cut shell the longitudinal part leaves the
  routing difference of `bubble_sub_contact`, which the bound must carry. Acceptance: the bound must
  resolve the `q²` coefficient. An `O(a²)` estimate independent of `q` proves convergence at fixed
  `q` but is useless after division by `q²`. Numeric check (`tools/lattice_polarization_check.py`):
  the lattice minus continuum `q²` coefficient is `C a² (hi² − lo²)`, `C ≈ 1.38`, with exact `a²`
  scaling and no `q` dependence, so the route resolves the coefficient. The correction is not
  proportional to the transverse structure at `O(a²)` (lattice anisotropy), so the bound is
  component-wise; the contact's sinc factors contribute at the same order. Formal target:
  `|Π_lat,sub(q) − Π_cont,sub(q)|_{μν} ≤ q² · C' a² (hi² − lo²) + O(|q|³/lo)` on
  `2|q| ≤ lo`, `a·hi ≤ 1`. Done (OVERVIEW): pointwise ingredient bounds
  (`PolarizationIngredients`), per-root expansions in `x = a r·q/2` (`PolarizationTaylor`), the
  ingredients to second order (`PolarizationSplit`), each order against the continuum
  (`PolarizationOrders`), the exact assembly `L = L₀ + Lin + Q + R` with the odd part cancelling in
  the second difference (`PolarizationAssembly`), magnitudes (`PolarizationMagnitudes`), the rest
  cubic in `q` (`PolarizationCubic`), and the lattice `Q` against the continuum's by fraction
  differences (`PolarizationQDiff`). Left: (a) the numerator differences of `Q_diff` from the
  `PolarizationOrders` gaps and `symbol_gap`; (b) specialization on the shell with `u = e_μ`,
  `v = e_ν`: `n(w) ≤ 2|w|`, `a|k| ≤ 1`, `|q| ≤ |k|/2`, `S ≥ |k|²/2`, giving `|R| ≤ c|q|³/|k|⁵` and
  `|Q_lat − coefC| ≤ c a²|q|²/|k|²`; (c) the lattice symmetry `L(−q, −k) = L(q, k)`, continuity on
  the shell, and the bridge from `Fin 4 → ℝ` (`sq4`) to `ShellMoments`' `EuclideanSpace`; (d) the
  shell integral as in `polarization_window`.
- Construct the map from background `Config` to the `RecordSupply` stream used by `ReferenceSelection`. Physical allocation of the banks is a [machine-layer dependency](Machine/REVIEW-AND-NEXT.md).
- Establish shared group and trace normalization across spacings. Multi-pass root words are tracked in the machine review.
- Identify the directional-exponential completion with the on-site completion, or specify the conditions for their agreement.
- Establish mode and domain control for the real-space PDE limit, the integrated Hessian, the full real-space fermion field and interacting-field estimates.
- Lead coupling (if pursued): a microscopic derivation of how the generations couple to the leads of
  the charged-current transfer. The equal-width assumption itself is a flavour-model premise owned
  by `PMFlavor.TransferGenerator`.
