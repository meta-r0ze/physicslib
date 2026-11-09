# SCOPE — the open physics frontier

The Lean tree is the ground truth for what is *checked*; each module's
`REVIEW-AND-NEXT.md` lists that module's residues. This file is the cross-cutting map
of the **open physics questions** — where the papers discuss them (cloned under the
sibling `PM/`, `PM-1-Arch/`, … repositories), what the tree covers, and whether the
item is a postulate, scoped out, a conditional relation, or a missing construction.
Update it when a frontier closes.

For the **consolidated, prioritized register** of every open item — with, for each,
why a reader flags it, what E8/persistence would have to produce, and the quickest
test — see [`OPEN-PROBLEMS.md`](OPEN-PROBLEMS.md).

## The model in one line
One finite E8 substrate + persistence (survival / hazard / selection). E8 values are
derived, then compared to SM values by `tools/e8p`.

## Coverage map

| Question | Papers | Tree status | Kind |
| --- | --- | --- | --- |
| Born rule (probability from amplitudes) | PM-2 `3_appendix_qm_fundamentals.tex` — "no Born-rule theorem … claimed"; `PMElementaryParticles.InclusiveMixing`, `PMAction.Machine.InterferenceReadout` | open | **postulate** |
| Measurement, basis selection, collapse | PM-2 `3_appendix_qm_fundamentals.tex` §Measurement; `PMAction.Measurement` | **built**: joint `⊗` space + controlled unitary interaction + pointer readout, and the **Born rule derived** (`born`); paper says the rule "can be stated once an observable, probability law and apparatus interaction are supplied" — now supplied | **construction done** (capacity-exhaustion / log2 preferred-basis still open) |
| Entanglement / Bell / no-signalling | PM-2 `3_appendix_qm_fundamentals.tex` §Correlations; `PMAction.Entanglement` | **partial**: two-system joint space, the Bell singlet, perfect correlation and entanglement (`singlet_not_product`) — the paper's "joint state space" need. **Built**: joint space, Bell singlet, perfect correlation, entanglement, and **no-signalling** (`no_signalling_singlet`: the singlet's marginal is `1/2` for a `Z` or `X` distant measurement). **Built**: joint space, Bell singlet, perfect correlation, entanglement, no-signalling, **and the CHSH inequality** (`chsh_eq`: the singlet's CHSH combination is `2√2`; `chsh_violates`: `2 < |CHSH|`, exceeding the local bound) | **constructed** |
| Lorentzian signature `(+,−,−,−)` | PM-1 `DerivedParameters.signature_witness`, `CliffordSignature` | postulated, not derived | **postulate** |
| Lorentz invariance / violation bounds | PM-1 `1_appendix_geometric_origins…`, PM-2 `2_entropic_action`; `PMElementaryParticles.PairIsotropy` ("Lorentz covariance … not asserted") | **partial**: `PMAction.D4Isotropy` proves the link directions (D4 roots / 24-cell) match a rotation-invariant distribution through **degree 4** (`quartic_isotropic`), so the leading *anisotropic* correction is degree 6 (O(a⁴)); the hypercubic alternative fails already at O(a²) (`hypercubic_not_isotropic`) and is excluded. **Open**: a full gauge-action correction formula and O(4) restoration in the continuum limit (the file flags both) | **partly built; continuum O(4) restoration open** |
| Quantum Yang–Mills | PM-2; PM-3 `4_D_temporal_allocation`, PM-5 `7_composites` | **mostly built**: finite-volume Euclidean Gibbs measure (`LatticeGibbs`), gauge invariance (`GeometricGauge.gibbs_preserving`), site-reflection positivity (`ReciprocalReflection.reflection_positive`), classical continuum limit (`LatticeSiteAction`), finite OS core (`Reconstruction`). **Open**: the Osterwalder–Schrader reconstruction from reflection positivity (transfer matrix / Hilbert space), infinite volume, renormalized continuum, mass gap | **partly done; the general-QYM remainder out of scope** (AGENTS) |
| Cosmological constant / vacuum energy | PM-6 `5_dark_sector.tex`, PM-3 `6_geometric_depth`; `PMCosmology.Thermodynamics`, `Hypotheses` | conditional relations only | **model input** |
| Dark matter / dark energy (nature, dynamics) | PM-6 `5_dark_sector.tex`, PM-2 `7_tol_mar_spactime`; `PMCosmology.Scaling.darkRatio = 31/6` | count only, no dynamics | **model input** |
| Inflation / primordial spectrum / initial state | PM-6 `Modes` (`amplitude_free`, `power_free`), `Primordial` | open (source free) | **model input** |
| Full gravity (metric, Einstein eq., diffeomorphisms) | PM-2 `WeakField` (weak-field only), PM-6 `SubstrateLoad` | open | **missing construction** |
| Electroweak hierarchy / naturalness | PM-1/PM-3 (Higgs from `2λv²`) | not addressed (only the value) | **open** |
| Grand unification | PM-3 (a GUT-scale number only) | no group/dynamics | **open** |
| CPT | PM-2 `CPPhases` (T only) | not a theorem | **open** |
| Origin of the complex structure (why ℂ amplitudes) | PM-2 amplitudes | model choice | **postulate** |
| Electromagnetic matching `α⁻¹(0) = Z_geo` | PM-1 `7_correspondences.tex` §EM matching; `PMConstants.ResponseMatching` | **closed**: the constants layer *defines* `α` as the substrate's admittance (`CertifiedConstants.α := causalCoupling`), so `α⁻¹ = Z_geo` is a theorem and the impedance form is the rationalized-units normalization `g² = 4πα` (`matching_frontier_iff_admittance`); equivalently the electric calibration (`matching_frontier_iff_calibration`) | **closed (definition/calibration)**; physical residual = the identification `α = κ` |

## How each kind is closed
- **postulate** — state it once and stop calling it derived; the tree already flags
  Born rule / signature this way inside modules.
- **out of scope** — state once, as the Yang–Mills note does in `AGENTS.md`.
- **conditional relation** — derive the "if input X then output Y" (already done for
  the VEV, the interface correction, the cosmo rescaling; more is listed in the
  module `REVIEW-AND-NEXT` files).
- **missing construction** — build the object (joint state space, metric dynamics).

## Where the choices can be eliminated
`PersistenceMechanics/SelectionSymmetry.lean` gives the test: a model choice is
*derivable* iff the relevant symmetry is **discrete** and its cost forces a **unique
minimizer** (`unique_minimizer_fixed`). Discrete examples that close this way:
sector exchange (`SectorExchange`), the μ–τ balance
(`ReferenceFlavour.reference_z2_balance`), the uniform law (`LawSelection`).
Continuous symmetries (the CP-sign phase conjugation,
`ReferenceSelection.invariant_cost_tie`) provably tie and need a symmetry-breaking
input.
