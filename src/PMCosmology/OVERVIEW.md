# PMCosmology — overview of checked results

The single map of what Paper VI proves and what remains an input or a draft-stage
proposal. Open work is in [`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md); build
instructions are in [`README.md`](README.md). Sources are under `PMCosmology/`,
imported by `PMCosmology.lean`. Theorem names are entry points, not exhaustive lists.
This is the most draft-stage paper, so the "risks" section is as important as the
"proved" section.

## Module map

| Module | Checked result | Retained inputs |
| --- | --- | --- |
| `Scaling` | Exact ratios `L = 1491/1376`, tilt `31/32`, dark ratio `31/6`; conditional Hubble/clustering rescaling; local index bounds | The additive weights and the response rules |
| `Tensions` | Certified propagated uncertainties `(1/2)L`, `(13/1000)/L` and the dark count `248/(48(1−2/43+α))` enclosure; dark-count `31/6` vs `25/6` (in `Scaling`) | Frozen inputs `0.5`, `0.013`, `5.36`; `α⁻¹` bounds |
| `PersistenceSelection` | Reuses `PersistenceMechanics.Selection`: `higher_rate_vanishes`, `least_rate_takes_over`, `uniform_law_selected` — persistence selects the least-cost member of an explicit family; no re-proof | The option family and its cost |
| `Hypotheses` | `CosmoModel` bundles the load/response/continuity premises and re-derives product invariance, `w`, vacuum-iff, and the headline `H_late` | The premises themselves |
| `SubstrateLoad` | 172 coordinate slots, one-slot complement of the payload fraction, exact revised outputs and tight bounds, fixed-load error propagation, joint product constraint | The load's cosmological interpretation |
| `InformationCapacity` | Saturated finite storage cannot injectively absorb a fresh label without extra capacity; recoverable initial states and input histories require at least C₀ bᵗ final states (m + t cells for m initial binary cells and one fresh bit per tick); independent-cell counts; conditional area law | No continuum metric/radiation process |
| `Saturation` | Residual-capacity speed, zero at capacity, exact weak-load remainder, strict two-load mean-index inequality | The local capacity law (no metric/horizon) |
| `Background` | Matter/radiation equality at `1+z = ρ_m/ρ_r`; density derivative and `w = −1 − aL'/(3L)` under supplied continuity | Dilution laws, load=density, continuity |
| `Readout` | `HomogeneousReadout`: scale factor = cube root of a comoving cell's volume (`a³=V`); density `N/V = PM-2 Continuity.homogeneousDensity N a`; matter `w=0` from conservation | The expansion history `V(a)` |
| `Modes` | **Substrate mode is E8-grounded**: `substrate_mode_evolves` re-exports `PMAction.RealSpaceFourier.hat_update` (Fourier blocks of the actual split update). The generic `A cos(kt+φ)` is only an ODE test function for the negative result (`amplitude_free`, `power_free`) | Initial data / source (the physical spectrum) |
| `Continuity` (PM-2) | Reused: a conserved comoving charge gives `matter_continuity` (`aρ'+3ρ=0`) and `w=0,1/3,−1` for matter/radiation/vacuum | Which per-particle scaling holds; the expansion |
| `Thermodynamics` | Entropy derivative, first-law temperature, conditional `1/(8πM)` comparison, cell-area normalization | Geometry, entropy coefficient, energy law |
| `Primordial` | Tilt/channel link, 32→16 non-injectivity, retained binary record, two CP-to-baryon windows, baryon-label conservation, source-free oscillator counterexample | A baryon-changing law and dilution |
| `NeutrinoCompatibility` | No common-scale/relabeling tower fits both fixed windows; factor-six excluded upstream | A derived nonuniform propagation law |

## The certified numbers

The paper's conditional rescalings, with the load `L = 1491/1376`:

- `SubstrateLoad.revised_numerical_outputs` — `67.4·L = 502467/6880` and
  `0.832/L = 143104/186375` (paper: `73.032994186…`, `0.767828303…`).
- `SubstrateLoad.revised_numerical_bounds` — tight enclosures
  `73.03299 < H_late < 73.03300` and `0.7678283 < S8_late < 0.7678284`.
- `SubstrateLoad.load_from_budget_terms` — `L = 1 + channelStress + boundaryStress +
  manifoldStress`; `Scaling.joint_rescaling_invariant` — the product `H·S8` is
  exactly invariant.

These certify the **arithmetic** given the frozen inputs and the response rules.
They do not derive the load, the response rules, or the inputs.

## Primordial CP input

`Primordial.baryon_ratio_reduced` fixes the conversion `η_B(J) = J/(16168π)`.
Paper IV's unitary CKM invariant `pmJ ≈ 3.02287×10⁻⁵` gives `5.951…×10⁻¹⁰`; the
older geometric `pm3J ≈ 3.08490×10⁻⁵` gives `6.073…×10⁻¹⁰`
(`baryon_windows`). The draft reference is `(6.12 ± 0.04)×10⁻¹⁰`; the matrix
input is ≈4.22 quoted errors away. A CP invariant alone is not an asymmetry
(`conserved_baryon`).

## Persistence selection (reused from `PersistenceMechanics`)

The selection principle is **not** re-proved here: `PersistenceMechanics`'
`PersistenceMechanics.Selection` proves it (`selection_principle`, `selection`,
`selection_timescale`), with `HazardForm` deriving the cost-proportional hazard and
`Gibbs`/`LawSelection` giving the zero-temperature and law-selection limits.
`PersistenceSelection` states the cosmology-facing corollaries:
`higher_rate_vanishes` (a dearer option's survivor share → 0), `least_rate_takes_over`
(the least-rate candidates dominate the surviving ensemble), and
`uniform_law_selected` (the uniform law survives average-cost selection).

**Where this helps, and where it does not.** Persistence turns a *choice* into a
*forced outcome* only when there is an explicit option family and a cost. For the
homogeneous state/readout (B1) and baryon symmetry (B4) the substrate state space
exists, so persistence or reversibility constrains it. For `L(a)` (B2), the
primordial spectrum (B3), the metric (B5) and the entropy law (B6) there is no
option family yet — those are coarse-grained dynamics that must be supplied before
persistence can rank anything.

## Draft-status risks / possible bugs

- **Headline numbers are rescalings of frozen inputs**, not a derivation. `67.4`
  and `0.832` are draft inputs; the response rules (`H·L`, `S8/L`) are
  constitutive. The exact product invariance means `H_late` and `S8_late` cannot be
  tuned independently — a constraint, not support.
- **CP-to-baryon discrepancy.** The two candidate CP inputs give `5.95` vs
  `6.07` ×10⁻¹⁰, both below the draft `6.12`; the matrix input is ≈4.22σ away.
  Selecting the closer number is not a resolution.
- **Dark-ratio ambiguity.** `Scaling.darkRatio = 31/6`, but the draft also refers
  to a `25/6` count; which count (total vs inactive) is `Ω_DM/Ω_b` is unresolved
  (see REVIEW).
- **No expansion history, growth model, perturbation spectrum, metric, horizon or
  entropy normalization** is derived; those are model inputs (Part B).
- **Neutrino factor-six** and any common-scale tower are excluded by the upstream
  oscillation windows; a nonuniform derived propagation law is not excluded.
- `check_load_consistency.py` evaluates the displays in floating point; only the
  quantities in `SubstrateLoad`/`Primordial` are Lean-certified.

## Verification

Run `./build.sh PMCosmology`. Permitted axioms `propext`, `Classical.choice`, `Quot.sound`.
