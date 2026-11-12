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
3. **The carrier–pion vertex**, if the `g_A` emission route in PMHadrons needs it: the pion couples
   to the carrier's axial current.

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
