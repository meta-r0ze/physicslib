# PMCosmology — open work (todo)

Checked mathematics and the certified numbers are in [`OVERVIEW.md`](OVERVIEW.md).
This file is only what remains, split by what a Lean proof can close (**Part A**)
and what needs a physical/model law (**Part B**). Paper VI builds clean; run `./check.sh` for current counts. This is
the most draft-stage paper, so also read **Draft-status risks** first.

## Draft-status risks / possible bugs

- `H_late`, `S8_late` are **conditional rescalings** of frozen draft inputs
  (`67.4`, `0.832`) under constitutive rules (`H·L`, `S8/L`); they are not an
  expansion-history derivation or a likelihood. `joint_rescaling_invariant` makes
  them a one-parameter constraint, so they cannot be independently tuned.
- **CP-to-baryon**: `pmJ` gives `5.95×10⁻¹⁰`, `pm3J` gives `6.07×10⁻¹⁰`, draft
  reference `(6.12±0.04)×10⁻¹⁰`; the matrix input is ≈4.22σ off. Choosing the
  closer number is not a resolution (`Primordial.baryon_windows`).
- **Dark-ratio count** `31/6` vs `25/6`: both are proved distinct (`Scaling`);
  which count is `Ω_DM/Ω_b` is recorded as an input (A1 done).
- **No** expansion history, growth model, perturbation spectrum, metric, horizon
  or entropy normalization is derived; all are Part B inputs.
- The Python display checker uses floating point; the PM-6-own quantities in
  `Scaling`/`SubstrateLoad`/`Tensions`/`Primordial` are Lean-certified.

## Part A — Lean-checkable gaps

### A1. Dark-ratio count `31/6` vs `25/6` — **Done**
`Scaling.disjoint_dark_count_check` proves `(248−48)/48 = 25/6` and
`darkRatio = 1 + 25/6 = 31/6`; `Scaling.exact_ratios` fixes `31/6`. The
`Ω_DM/Ω_b` identification is recorded as an input. No longer open.

### A2. Certify the remaining display arithmetic — **Mostly done**
Proved: `SubstrateLoad.revised_numerical_outputs`/`_bounds` (`H_late`, `S8_late`);
`Tensions.hubbleInputSigma_*` (`(1/2)L`), `s8InputSigma_*` (`(13/1000)/L`),
`omegaRatio_bounds` (`248/(48(1−2/43+α))`); and
`Background.geometric_equality_requires_ratio` (`ρ_m/ρ_r = 1+1075π`). Remaining
tags are reused upstream quantities (`α`, masses, …) generated in `cosmology.py`
but owned by Papers I/IV/V; certifying those in PM-6 would duplicate their
upstream proofs.

### A3. Hypothesis ledger — **Done**
`Hypotheses.CosmoModel` bundles the load, both response rules, the
load-proportional density and the separately conserved continuity law in one
structure; `product_invariant`, `equation_of_state`, `density_derivative`,
`vacuum_iff` and `headline` are re-derived from it. The premises are now a
machine-checkable input list. (Entropy laws remain an explicit Part B input.)

## Part B — physical model inputs

**Persistence is not a free choice where an option family and cost exist.** The
selection principle is already proved in `PM/lean` (`PersistenceMechanics.Selection`);
`PersistenceSelection` reuses it (`higher_rate_vanishes`, `least_rate_takes_over`,
`uniform_law_selected`). So each "choose X" below should first be asked as: *is X
the least-cost member of an explicit option family?* For (1) and (4) the substrate
state space exists, so persistence/reversibility constrains them. For (2), (3),
(5), (6) there is **no option family yet** — the coarse-grained dynamics must be
supplied before persistence can rank anything; that is the real missing input.

1. **Homogeneous state, physical clock and readout.** `Readout.HomogeneousReadout`
   now *defines* the scale factor as the cube root of a comoving cell's volume
   (`a³=V`) and ties the density to PM-2 `Continuity` (`w=0` for a conserved
   charge). Remaining inputs: the expansion history `V(a)`, the pressure/energy
   readout, and how `H0`/`S8` are inferred from it. A dimensionless `23/43` ratio
   still cannot supply absolute Hubble units.
2. **Background conservation and evolution.** The continuity relation is now
   *derived* upstream, not assumed: PM-2 `Continuity` takes a conserved comoving
   charge (substrate `RegisterHamiltonian.evolution_occupation`) to density
   `N/a³`, proving `matter_continuity` (`aρ'+3ρ=0`) and the equation-of-state
   values `matter_w`/`radiation_w`/`vacuum_w` (`w=0,1/3,−1`). So `w` follows from
   conservation plus one per-particle scaling. Remaining inputs: which scaling
   holds (matter/radiation/vacuum), whether sectors exchange energy, and the
   expansion `a` / `L(a)` itself.
3. **Primordial perturbation state and spectrum.** The substrate mode structure is
   E8-grounded and re-exported: `Modes.substrate_mode_evolves` is
   `PMAction.RealSpaceFourier.hat_update` (Fourier blocks of the actual split update).
   The generic `A cos(kt+φ)` is only an ODE test function; it shows the negative
   result that a source-free linear equation does not fix the amplitude/power
   (`amplitude_free`, `power_free`). `31/32` remains a channel-overhead complement,
   not a spectral calculation; the physical source/initial state is still an input.
4. **Baryon-changing dynamics and a particle spectrum.** A CP invariant alone is
   not an asymmetry. Grounded upstream now: PM-3 `BaryonNumber` defines baryon
   number on the 16 channels from the axis ledger (`B−L = ReferenceAxis.bl`) and
   proves native reversible gates conserve total baryon
   (`PMConstants.BaryonNumber.no_asymmetry_from_reversible`). So an asymmetry needs a
   *non-baryon-preserving* (irreversible) event, not a CP phase. Derive the event, conservation channels,
   initialization and dilution factor; reconcile the unequal CP formulas rather
   than selecting; derive (or replace) a nonuniform neutrino propagation law
   before imposing the floor.
5. **Metric and global causal structure for saturation.** The weak-field part now
   exists upstream: PM-2 `WeakField` checks the reconstruction `g_00 = −(1+2Φ)`
   for the capacity-ledger candidates and `Φ = −K/ν + K²/(2ν²)` (strictly
   attractive). Still open: the response law selecting the readout, the spatial
   metric, the field equation, and a *global* causal structure (a horizon needs a
   Lorentzian spacetime Mathlib does not provide). Local index convexity is not
   Birkhoff violation; a zero local clock speed is not an event horizon.
6. **Entropy and dark-sector normalization.** The area count gives `log(q)/a`, not
   automatically `1/(4ℓ_p²)`. Conditional first-law consistency is not a Hawking
   state, evaporation or information recovery. Resolve the total/inactive count
   ambiguity and component occupations before counts become abundance ratios.
7. **Joint test.** Only after a specified background, perturbations and readout
   exist can cosmological likelihoods/evidence be compared; the present
   fixed-input residuals are not that test.

## Suggested order

Part A is closed (A1, A3 done; A2 covered for PM-6-owned tags). Remaining work is
all Part B:

1. **Part B 1–2** (state/readout, background `L(a)`) — the shared model a joint
   test needs.
2. **Part B 3–4** (primordial spectrum, baryon-changing dynamics).
3. **Part B 5–6** (metric/causal structure, entropy/dark-sector normalization).
4. **Part B 7** (joint likelihood).

## Verification

Run `./check.sh`. Permitted axioms `propext`, `Classical.choice`, `Quot.sound`.
