# PMAction — open work

Checked mathematics, the module map and everything established are in
[`OVERVIEW.md`](OVERVIEW.md). This file lists only what remains.

## A. Hadron-facing

1. **The carrier's rms radius in Lean.** `PMHadrons.CubeScales` uses the carrier's rms radius
   (`1.354` sites on `3³`, numerical, `tools/confined_walk.py`); its theorems assume only `ρ ≥ 1`.
   A Lean value needs the lowest eigenvector of the confined two-slice Hamiltonian.
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

   Open, in order: (a) why the cube's `g_A` is `8%` above `5/4` with the persistence-consistent
   boundary (candidates: the cube's site count — `4` sites per edge gives `1.265`; the finite
   tick; the carrier's own mass); (b) the cube's colour coupling.
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
