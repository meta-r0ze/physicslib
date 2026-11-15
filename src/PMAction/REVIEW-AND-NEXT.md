# PMAction — open work

## Generation sector

The six-step plan is done, and the wire's mass form is derived (OVERVIEW: `GenerationSector`,
`CarrierFlip`, `ReferenceDetuning`; `PMAction.ReferenceWallMass`: `M = D_R (δ_O + cyc κ_O)`). How
each species uses the wire is protocol work in
[PMElementaryParticles](../PMElementaryParticles/REVIEW-AND-NEXT.md). The node amplitude is
derived (`PMAction.NodeAmplitude`: `k/K = α/2`). Open, wire only:

- **Size of the other wall's detuning.** `ReferenceDetuning` puts the reference's wall at the
  Wilson point (`δ_R = 0`), so the seesaw term `δ_F δ_T Y⁻¹` vanishes and the light mass is
  `D_R (δ_O + cyc κ_O)` with no competing direct term on the reference's wall. The other wall's
  detuning `δ_O` (in `ZeroModeCoupling`'s terms, its departure from `r = 1`) sets the mass scale and,
  relative to the carriers, the mixing. It must be nonzero: at `δ_O = 0` the mass is a cyclic shift
  with masses `(kK, k², kK)`, two heavy and one light (`PMAction.UndetunedWall`), the reverse of
  the observed ordering. Find what fixes its size on the substrate; the library has no source yet.
  Once it is fixed the wire has no free number, and the persistence rotation `U` of each protocol
  (how far persisting states turn from the label states; PMFlavor's `U_uᴴ J U_d`) can be bounded.
  Already without it (`ReferenceWallRotation`): on the reference's wall every off-diagonal entry of
  `M Mᴴ` is `dᵢ(δ̄ κ + δ κ̄)d̄ⱼ`, so the rotation there is about `|dᵢ/dⱼ| · |κ_O/δ_O|`, suppressed by the
  label states' mass ratio; the charged current reads that side (rows of `D₂ Y⁻¹ D₁ᴴ` are the reference's wall, which `(1 − Γ)/2` selects; one step by name).
  **What the library already says about `δ_O` (numerical, outside Lean, 2026-11).** Units: flips in
  the `δβ` slot, so a carrier of hop amplitude `t` is `−r t/2` (`CarrierFlip`); `NodeAmplitude`'s
  "amplitude is admittance" with `K = 1` makes the vector flip `K_f = r/2` and the spinor flip
  `k_f = rα/4`.
  1. *Ordering.* `M = D_R (δ_O + cyc κ_O)` with the symmetric amplitudes (`UndetunedWall`'s
     bookkeeping) has one heavy and two light singular values once `|δ_O| ≳ k_f`; at `δ_O = 0` it is
     reversed (`UndetunedWall`). So the ordering needs `δ_O ≠ 0`, not `δ_O` dominant.
  2. *Light pair.* With `|κ_R(s)| = |κ_R(c)|` (`NodeAmplitude`: one magnitude on both walls) the light
     pair is degenerate for every `δ_O` (ratio `> 0.99` for `|δ_O| ≥ 0.1 K_f`; also with the repair
     sign), and the reference-wall persisting states of labels `1`, `2` are `45°` mixtures. So the wire
     alone gives a maximal persistence rotation in the light block; a light-pair split (protocol,
     PMElementaryParticles) is what makes it small, then `θ₁₂ ≈ (m₁/m₂) · k_f/|δ_O|`.
  3. *Heavy–light.* `θ₁₀ ≈ (m₁/m₀) · K_f/|δ_O|`, so `ε = K_f/|δ_O| = r/(2|δ_O|)` in hop units. The
     light-mode reduction (Schur complement) needs the flips small against the crossing link,
     `|δ_O| ≪ |y|`. PMFlavor's `U = 1` tests need `ε ≲ 0.04`, so `|δ_O| ≳ 12` and `|y| ≫ 12`: the crossing
     link much stronger than one lattice hop. If the crossing amplitude is itself an admittance
     (`≤ 1`, the carriers' normalization), `ε > 1/2` and `U` must be computed, not set to `1`.
  So the open numbers are `|δ_O|` and `|y|` in hop units (or their ratio and `t_v`), and the
  light-pair split. Candidate sources to examine: what normalizes the equal-class crossing `y`
  (`GenerationParity`), and whether the other wall's chiral zero mode bounds `|δ_O|`. Also open: whether it is a wire constant or set by
  what a protocol occupies on that wall. Upstream of PMFlavor's "The wire's own mixing" and
  PMElementaryParticles' "Species masses over the wire".

- **Update as `e^{−iHt}` on wall modes.** `PMAction.FlavourEvolution` takes the flavour evolution as
  `U e^{−iEt} Uᴴ` with supplied `U`, `E`, and the transfer-cost chain in PMFlavor
  (`ReferenceSelection` → `RelativeFrameCost` → `TransferWorkLaw`) is built on it.
  `WallLatticeSpectrum` states the gap: the finite-tick substrate update is not identified with the
  wall Hamiltonian's exponential, and no physical clock is fixed. Show whether the update at the
  clock acts on the wall modes (`NativeFlavourWall`) as `e^{−iHt}` for some `t` set by `Δ`; until
  then the transfer-cost results are conditional on it. Falsification: an update whose action on
  the light wall modes is not a function of `H` alone.

## Carrier update

- Certify the lowest positive carrier level on the full 216-dimensional operator, then certify the spin-up rms radius in Lean. The exact subspace calculation is in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`; the full-space level ordering still uses floating point.
- Find the physical axial current of the carrier. The two-slice update's own local axial rotation is the slice sign: it commutes with every hop and the on-site term and is broken only by the inter-slice coupling, and its link current `sym(S v_j)` is exactly normalized for free carriers (`tools/slice_axial.py`). On the confined carrier it gives `0.22–0.45` (`n = 3…8`) against the on-site `Σ_z` `0.83–0.67`, extrapolating to about `0.5` against `0.65`: with two slices the wall leakage is `O(1)`, so this current neither confirms the on-site operator nor gives a usable `g_A`. Next candidates: the many-slice limit of the wall, or the vector-axial Ward identity at nonzero momentum transfer. The [hadron calculation](../PMHadrons/REVIEW-AND-NEXT.md) needs this current and pion source.

## Dynamics and limits

- Lattice polarization, optional sharpening (OVERVIEW: `PolarizationShellIntegral`). (i) Replace the
  continuum shell by the Brillouin-zone sum, where the routing difference of `bubble_sub_contact`
  cancels by a shift. (ii) A sharper constant than `K = 271853128/3`, so that the bound gives the size
  of the lattice correction at a fixed `a`. The numeric target is `C a² (hi² − lo²)` with `C ≈ 1.38`
  (`tools/lattice_polarization_check.py`). Falsification: a proved constant below `1.38` would
  contradict the numeric check.
- Construct the map from background `Config` to the `RecordSupply` stream used by `ReferenceSelection`. Physical allocation of the banks is a [machine-layer dependency](Machine/REVIEW-AND-NEXT.md).
- Establish shared group and trace normalization across spacings. Multi-pass root words are tracked in the machine review.
- Identify the directional-exponential completion with the on-site completion, or specify the conditions for their agreement.
- Establish mode and domain control for the real-space PDE limit, the integrated Hessian, the full real-space fermion field and interacting-field estimates.
