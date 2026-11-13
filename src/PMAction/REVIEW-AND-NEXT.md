# PMAction — open work

Checked mathematics, the module map and everything established are in
[`OVERVIEW.md`](OVERVIEW.md). This file lists only what remains.

## A. Hadron-facing

1. **The carrier's rms radius — certified outside Lean (Nov 2026).** `tools/carrier_rms_certificate.py`
   computes it with exact arithmetic (Gaussian rationals) and interval arithmetic, no floating
   point: the spin-up ground mode lies in a 28-dimensional cyclic subspace of `H`; `E₀` is a root
   of a degree-14 integer polynomial in `[0.84119, 0.84120]`; the eigenvector is the exact
   polynomial in `E₀` from the subspace's minimal polynomial; `ρ = 1.3535970389792…` sites
   (`PMHadrons.CubeScales` needs only `ρ ≥ 1`). That `E₀` is the lowest positive level overall is
   checked in floating point (next level `1.4554`). A Lean proof would need exact arithmetic on
   the 216-dimensional operator and its powers in the kernel (`native_decide` is not among the
   permitted axioms), so it is deferred as a certified-numerics task; the plan (root interval,
   invariant subspace, eigenvector as a polynomial in `E₀`) is in `tools/carrier_mode_exact.py`.
2. **The contact running on the lattice (optional).** Everything in `(3α/4π)(1 + 2Q̄)` is derived
   except the Feynman parametrization step and the identification of the leading-log region with
   the D₄ lattice sum far below the cutoff. Low priority: `R` already matches the pion to `7×10⁻⁵`.
3. **The carrier cube's `g_A` and colour coupling (Nov 2026; status, details in
   `PMHadrons/PILLARS.md`).** E8's `5/4` is the strong-interaction axial charge (lattice QCD
   `1.246(28)`; the measured `1.2754` carries a `1.4–2.6%` electromagnetic correction). On the
   substrate: the carrier resolved inside the 3-cell hadron volume and projected to zero total
   momentum gives `≈ 1.34`; a source-confined pion cloud (`−5` to `−8%`) brings it to
   `≈ 1.24–1.28`, with no fitted parameter. Open: (a) recompute the cloud with the fine carrier as
   its source; (b) derive the pion source from the local axial variation of the two-slice update
   (wall and inter-slice terms kept; this also settles the axial normalization, so far only checked
   for free carriers); (c) the Toll rule for a pion pair that leaves the host and returns;
   (d) the colour coupling on the cube, which perturbative running cannot reach (one loop gives
   `α_V ≈ 1.3`). Resonances (the Δ) are out of scope: hosted transients with negative Margin.

## B. Foundational (long-term)

1. **The reference/record banks.** A formal map from the background `Config` to `RecordSupply`'s
   stream (an identification in `ReferenceSelection`'s docstring), and the physical allocation of
   the banks.
2. **The microscopic hop.** Shared group/trace normalization across spacings; edges carrying
   several passes of the root generators (the staggering of `Machine.RootWordControls` with more
   sub-intervals, not formalized). The settled parts (root words for the generators, the axis hop,
   the gate's coherent step, the C² controls) are in [`Machine/OVERVIEW.md`](Machine/OVERVIEW.md).
3. **The directional-exponential completion** is not yet identified with the on-site one.
4. **Full field and integrated limits.** Real-space field/PDE mode–domain control, the integrated
   Hessian, the full real-space fermion field, interacting-field estimates. Probably not needed for
   lattice predictions.
5. **Applications beyond the decays.** Gravity and measurement need their own
   state/update/observable; the quantum continuum and Lorentzian continuation are distinct
   obligations.

## Out of scope

The quantum Yang–Mills constructions (transfer matrix, infinite volume, full O(4) restoration,
renormalized continuum, continuum mass gap); see the scope note in [`OVERVIEW.md`](OVERVIEW.md).

## Downstream boundary

Generic proofs do not move a downstream paper's physical identification with them. Paper III owns
packet representations and constants; Paper IV flavour/mass; Paper V decay/phase-space; Paper VI
cosmology.

## Verification

Run `./build.sh PMAction` and `./build.sh audit`. No Paper III–VI imports; permitted axioms
`propext`, `Classical.choice`, `Quot.sound`.
