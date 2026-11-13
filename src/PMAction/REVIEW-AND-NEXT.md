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
3. **The colour coupling on the carrier cube (open, Nov 2026).** `tools/colour_fluctuation.py`
   computes one-gluon exchange among the three confined carriers (ground mode, singlet factor
   `−2/3`, `CubeGreen3` propagator). With the ledger coupling `α_s = 0.118` on the cube, the
   `g_A` correction is `−0.16%` and the N–Δ splitting is `6 MeV` (observed `293 MeV`). So the
   argument "the same dimensionless lattice coupling on every persistent cube" is contradicted by
   the N–Δ splitting: the observed splitting needs an effective `α_s ≈ 5.6` on the carrier cube.
   Both effects are linear in the coupling, so their ratio is coupling-free: calibrated by the
   observed `293 MeV`, first-order exchange gives `g_A ≈ 1.27` (measured `1.2754`), i.e. the `+8%`
   is the same hyperfine physics that splits N and Δ. Caveats: first order at a large coupling,
   positive-energy modes only, static propagator.

   **Running to the cube (Nov 2026, `tools/cube_coupling_running.py`).** Persistence says where
   the coupling is read: colour is read at the executing mass (`PMConstants.ReadScale`), so the
   carrier cube reads it at `1/a = 318 MeV`, not at the Z. Every input to the running is already
   in the library: `α_s(m_Z)`, the derived one-loop `b₀ = 11N/3 − 2n_f/3`
   (`RunningCoefficients.b0`), and the thresholds at the E8 masses `m_c = 1267 MeV`,
   `m_b = 4182 MeV` (`PMConstants.StrongRunning`). One loop gives `α_s(1/a) = 0.87`, with
   `Λ₃ = 142 MeV`, so `1/a ≈ 2.2 Λ₃`. Two loops (continuum `b₁`, as a stability test) reach a
   pole near `400 MeV`, above `1/a`. So the scale is now fixed by persistence, but the value is
   not: the carrier cube sits in the non-perturbative region, where running does not determine
   the coupling. The needed effective `5.6` is above the one-loop `0.87`, as it should be there,
   but nothing yet derives it. Open: a non-perturbative colour computation on the `3³` cube itself
   (for example the static potential from Wilson loops at the cube's own coupling). No E8 value
   for the Δ mass exists yet, so the N–Δ calibration stays a comparison.

   **Target corrected (Nov 2026).** The carrier computation gives the strong-interaction axial
   charge, so its target is lattice QCD's `1.246(28)`, not the measured `1.2754`, which carries a
   `1.4–2.6%` electromagnetic correction (PMHadrons REVIEW §0). E8's `5/4` sits on the lattice
   value.

   **Boundary condition for the colour field (Nov 2026) — retracts the `1.27` above.** The
   exchange above used the Dirichlet Green function (field zero on outside sites), which links the
   cube to sites it does not refresh. The carrier uses the opposite rule: no link out of the cube
   (`ConfinedCarrier`, plain truncation). Applied to the colour field, no link out means no colour
   flux leaves (`n·E = 0`, Neumann for the electric part) and, for the magnetic part, component
   `k` has no link out along axis `k` (`n×B = 0`). These are the bag-model conditions, here from
   the lattice rule. With them (`tools/colour_fluctuation.py`, now the default; `BC=D` for the
   old one): N–Δ is `12 MeV` at `0.118`, so the observed `293 MeV` needs `α_s ≈ 2.9` (Dirichlet:
   `5.6`; MIT bag fits: `≈ 2.2`), and at that coupling exchange moves `g_A` by only `−1.7%`, to
   `1.353`. So one-gluon exchange does **not** close `g_A`; the Dirichlet result was an artefact
   of the boundary. The cube's `g_A` is `1.35–1.38` against lattice QCD's `1.246(28)`.

   **The Δ has no occupancy mass.** Masses in PMHadrons are occupancy costs of persistent
   placements (`Occupancy`). The Δ decays strongly (`Γ ≈ 117 MeV`, lifetime `≈ 5.6×10⁻²⁴ s`),
   about 3 time steps of the carrier cube (`ħ/(318 MeV) ≈ 2.1×10⁻²⁴ s`), far less than one
   `Δ = 43`-step cycle. It is not persistent, so the minimum-room rule does not give it a mass;
   its mass is a level of the carrier cube's dynamics, which needs the same colour coupling.

   **Candidate: the hadron cube has 4 sites per edge (Nov 2026).** With a hard wall the carrier
   is scale-free, so `g_A` depends only on the edge site count `n`: `1.377` (`3`), `1.265`
   (`4`), `1.195` (`5`), `1.153` (`6`), toward the continuum bag value `1.09`. A rule that would
   select `n`: `MinimalCube` asks for an interior vertex (a site all of whose links are the
   volume's own), and `Occupancy` places one carrier per cell. If each persistent carrier needs
   its own interior vertex, `k` carriers need `(n−2)³ ≥ k`: one carrier gives `n = 3` (the old
   lepton cube), two or three carriers give `n = 4`. On `4³` (`1/a = 434 MeV` from the
   carrier's rms radius `1.85` sites = `r_p`), with the no-link-out boundary, N–Δ needs
   `α_s ≈ 2.4`, and exchange at that coupling gives **`g_A = 1.246`** (lattice QCD
   `1.246(28)`, E8 `5/4`). Caution: the rule is proposed after seeing that `n = 4` fits, and the
   coupling is still calibrated by the observed Δ.

   **Verdict: not adopted — persistence as stated does not require it.** (1) `MinimalCube`'s
   criterion is one interior vertex for the *volume*; nothing in it is per carrier. (2) The
   carriers are not cell occupants in this computation: all three sit in the same spatial mode,
   and exclusion is met by the antisymmetric colour (`ColourSinglet`, `CarrierStatistics`), so a
   per-carrier site rule would contradict the model it is meant to fix. (3) "One cell per carrier"
   in `Occupancy` is the meson ledger's lower bound, stated as an input there, and the nucleon's
   base is the causal cone, not a cell count. (4) Economy picks the smallest valid volume, which
   is `3³`. So `n = 3` stands and the `8%` stays open. The `4³` number is kept as a sensitivity
   result: `g_A` is very sensitive to the carrier's resolution. Remaining candidates: virtual
   colour-singlet pairs inside the cube (a pion cloud; the Toll bound covers only real emission
   through the boundary), and the colour coupling without the Δ.

   **Tried (Nov 2026).**
   * *Pairs through colour exchange* (`PAIRS=1` in `tools/colour_fluctuation.py`: negative-energy
     intermediate modes, the Z-graphs): at the N–Δ coupling they move `g_A` by `+3.7%`, the wrong
     direction (net `+1.95%`, `1.404`). A pion cloud proper (a colour-singlet pair emitted by one
     carrier and absorbed by another) needs a carrier–pion vertex, which is not built.
   * *Which operator is the axial current* (`tools/axial_link.py`). A gauge boson couples to the
     walk through its links, so the spatial current is the velocity `v_z = i[H, z]`
     (point-split), and the axial one is `γ5 v_z`. On `3³` it gives `0.542` against the on-site
     `Σ_z = 0.826` (`g_A = 0.904` against `1.377`); the two converge only slowly as the cube grows
     (ratio `0.66, 0.74, 0.78, 0.80, 0.84` for `n = 3…8`). The target `0.75` lies between them.
     This is lattice QCD's `Z_A` problem: a bare lattice axial matrix element is normalized by an
     axial Ward identity before it is compared (typical `Z_A` for Wilson-type actions is below one;
     `5/4` needs `Z_A = 0.908` on the on-site operator).
   * *Normalization — partly checked (Nov 2026, `tools/axial_ward.py`).* A free carrier moving
     along `z` gives `⟨Σ_z⟩ = 1` (its helicity) at every momentum, and the link current gives
     `cos k`. That checks the on-site operator's spin normalization for free axial motion; it is
     not a Ward identity for the confined current (review by a second model, Nov 2026: the script
     also mixes the slice-odd `Sγ5` with the slice-even `γ5`). The decisive check, not yet done,
     is the local axial variation of the actual two-slice update with the wall and inter-slice
     terms kept; it could confirm the on-site operator without an adjustable `Z_A`.

   **Cross-checks that do not depend on the axial normalization (Nov 2026).**
   * *Magnetic moment* (`tools/proton_moment.py`; the vector current is conserved, so no `Z`).
     SU(6) gives `μ_n/μ_p = −2/3` (measured `−0.685`). The size is low: on `3³` with the carrier
     rms radius set to `r_p`, `μ_p = 1.74` n.m. (on-site current) or `1.04` (link current),
     measured `2.793`; larger `n` raises it slowly (`2.11` / `1.67` at `6³`). MIT bag fits are also
     low (`≈ 1.9`). So the carrier core is too small or too relativistic for `μ_p` while too
     non-relativistic for `g_A`: one cube does not fit both. In hadron models the pion cloud
     raises `μ` and lowers `g_A`, which is the direction both need.
   * *Goldberger–Treiman* `g_πNN = g_A m_N/F_π`: E8 `5/4`, `m_N`, `F_π = f_π/√2 = 92.1 MeV` give
     `12.74`; from `g_πN²/4π ≈ 13.7`, `g_πNN ≈ 13.1` (the usual `≈ 2%` GT discrepancy, plus the
     electromagnetic `2%`).
   * *Big gaps elsewhere that point the same way:* the singlet axial charge (quark spin fraction)
     is `ΔΣ ≈ 0.3` measured against `0.83` here (the axial anomaly; `PMConstants.ChiralAnomalies`),
     and hyperon decays give `F/D ≈ 0.58` against SU(6)'s `2/3`.
   So the strongest single lead is the pion cloud: it is the one mechanism that moves `g_A` down
   and `μ_p` up together. It needs the carrier–pion vertex, and that vertex is fixed by the same
   axial current (Goldberger–Treiman), so it and `Z_A` are one problem.

   *Pion-cloud estimate (Nov 2026, floating point).* One loop with the Goldberger–Treiman vertex,
   E8 `F_π = 92.1 MeV`, `m_π`, nucleon intermediate states only, and a dipole form factor:
   `δg_A/g_A = −(1+2g_A²)/(12π²F²) ∫k⁴u²/ω³` (normalized to the chiral log). The sign is right,
   but the size is set by the cutoff: `−19%`, `−39%`, `−65%` for `Λ = 600, 800, 1000 MeV`; the
   cube's own form factor (dipole matching `r_p`) gives `Λ ≈ 810 MeV`. The nucleon-only loop is
   known to overshoot: Δ intermediate states cancel much of it (exactly at large `N_c`), and there
   is no E8 Δ. So the cloud can supply the `−9%`, but not without the Δ sector; this is not yet a
   prediction.

   **Second-model review (Nov 2026) — what is fixed and what is not.**
   * *The ground-orbital Δ already exists.* Three carriers in the common ground doublet span the
     symmetric spin–flavour space `Sym³(4) = (S=I=½) ⊕ (S=I=3/2)`, dimensions `4 + 16 = 20`, both
     at energy `3E₀`. So the Δ multiplet is available without a Δ mass or occupancy rule.
   * *The N–Δ cancellation is fixed for the cubic term.* With `G^{ia} = Σ_q σ^i_q τ^a_q/4` and a
     common static source, the double commutator `Σ[G^{jb},[G^{jb},G^{ia}]]` equals `G^{ia}` on the
     full 20 states, but `(5/3)²` times it with nucleon-only intermediate states. Checked
     numerically here: `1.000` and `2.778 = 25/9`. So the full multiplet keeps `9/25` of the
     nucleon-only cubic term. This is not a factor for the whole `−39%` (the term linear in the
     coupling and nonzero splittings differ).
   * *The `−39%` is not a prediction.* Normalized to the chiral log, the integral still carries a
     `Λ²` piece whose split between core and cloud is free; a radius fixes a form factor's slope,
     not the emission matrix element across the zone.
   * *The cube cannot split N and Δ as it stands.* Independent carriers give `3E₀` to both; a term
     `cJ²` respects every symmetry and moves the splitting by `3c`. The economical source is the
     same pion interaction: its static self-energy contains `−K Σ G^{ia}G^{ia}`, and
     `Σ G² = 3.5625` on N and `2.0625` on Δ (checked here), so it makes the **nucleon lighter** by
     `1.5K` with no colour coupling or observed splitting as input. `K` needs the pion modes and
     source.
   * *Two persistence premises, different physics:* the host confines the pion **source** (pion
     propagates freely), or the host confines the pion **field** (discrete modes on the cube).
     The carrier's no-link-out rule does not by itself select the pion's boundary. Choosing it, the
     form factor, or `5/4` in the vertex because they give `−9.2%` would be a fit; the vertex should
     use the bare cube current.
   * *Null test:* `μ_n + (2/3)μ_p` vanishes at every resolution in the one-body common-orbital model;
     measured `−0.051` n.m. A purely isovector cloud shifts it by `−δμ_p/3`, so raising `μ_p` from
     `1.04` to `2.79` that way would overshoot it tenfold: a cloud must also change the isoscalar
     part. Caveat on `tools/proton_moment.py`: it sets the bare carrier radius equal to the dressed
     charge radius, which a charged cloud invalidates.
   **Plan:** (1) the local axial variation of the two-slice update (current and pion source from
   one update); (2) the degenerate 20-state second-order self-energy with that source, giving the
   vertex correction to `g_A` and `K` for the splitting, under each pion-boundary premise; (3) the
   magnetic null test on any proposed dressing.

   *Last perturbative try.* Converting the one-loop `α_s(1/a) = 0.87` to the static-potential
   scheme (`α_V = α(1 + a₁α/4π)`, `a₁ = 31/3 − 10n_f/9`) gives `α_V ≈ 1.3`, against the `2.9`
   the N–Δ splitting needs with the persistence-consistent boundary. The coupling on the cube
   stays a non-perturbative open item.
4. **The carrier–pion vertex** is no longer needed for `g_A`: real emission through the Toll
   boundary is `~10⁻⁵` (PMHadrons REVIEW).

## B. Foundational (long-term)

1. **The reference/record banks.** A formal map from the background `Config` to `RecordSupply`'s
   stream (an identification in `ReferenceSelection`'s docstring), and the physical allocation of
   the banks.
2. **The microscopic hop.** Which E8 root words the native generators come from; shared
   group/trace normalization across spacings; for the packet subsystem the `C²` control
   one-forms. (The gauge `β` and admission are settled: `EventCoupling` with
   `PMConstants.ChainCouplings`, and `Admission`, whose rule is a stated PM premise.)
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
