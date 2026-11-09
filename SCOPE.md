# SCOPE — the open physics frontier

The Lean tree is the ground truth for what is *checked*; each module's
`REVIEW-AND-NEXT.md` lists that module's residues. This file is the cross-cutting map
of the **open physics questions** — where the papers discuss them (cloned under the
sibling `PM/`, `PM-1-Arch/`, … repositories), what the tree covers, and whether the
item is a postulate, scoped out, a conditional relation, or a missing construction.
Update it when a frontier closes.

## The model in one line
One finite E8 substrate + persistence (survival / hazard / selection). E8 values are
derived, then compared to SM values by `tools/e8p`.

## Coverage map

| Question | Papers | Tree status | Kind |
| --- | --- | --- | --- |
| Born rule (probability from amplitudes) | PM-2 `3_appendix_qm_fundamentals.tex` — "no Born-rule theorem … claimed"; `PMElementaryParticles.InclusiveMixing`, `PMAction.Machine.InterferenceReadout` | open | **postulate** |
| Measurement, basis selection, collapse | PM-2 `3_appendix_qm_fundamentals.tex` §Measurement | open (needs observable + apparatus interaction) | **missing construction** |
| Entanglement / Bell / no-signalling | PM-2 `3_appendix_qm_fundamentals.tex` §Correlations | open (no joint state space) | **missing construction** |
| Lorentzian signature `(+,−,−,−)` | PM-1 `DerivedParameters.signature_witness`, `CliffordSignature` | postulated, not derived | **postulate** |
| Lorentz invariance / violation bounds | PM-1 `1_appendix_geometric_origins…`, PM-2 `2_entropic_action`; `PMElementaryParticles.PairIsotropy` ("Lorentz covariance … not asserted") | open | **falsifiable prediction to add** |
| Quantum Yang–Mills (mass gap, confinement, infinite volume) | PM-2 (classical limit only); PM-3 `4_D_temporal_allocation`, PM-5 `7_composites` | scoped out | **out of scope** (AGENTS note) |
| Cosmological constant / vacuum energy | PM-6 `5_dark_sector.tex`, PM-3 `6_geometric_depth`; `PMCosmology.Thermodynamics`, `Hypotheses` | conditional relations only | **model input** |
| Dark matter / dark energy (nature, dynamics) | PM-6 `5_dark_sector.tex`, PM-2 `7_tol_mar_spactime`; `PMCosmology.Scaling.darkRatio = 31/6` | count only, no dynamics | **model input** |
| Inflation / primordial spectrum / initial state | PM-6 `Modes` (`amplitude_free`, `power_free`), `Primordial` | open (source free) | **model input** |
| Full gravity (metric, Einstein eq., diffeomorphisms) | PM-2 `WeakField` (weak-field only), PM-6 `SubstrateLoad` | open | **missing construction** |
| Electroweak hierarchy / naturalness | PM-1/PM-3 (Higgs from `2λv²`) | not addressed (only the value) | **open** |
| Grand unification | PM-3 (a GUT-scale number only) | no group/dynamics | **open** |
| CPT | PM-2 `CPPhases` (T only) | not a theorem | **open** |
| Origin of the complex structure (why ℂ amplitudes) | PM-2 amplitudes | model choice | **postulate** |

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
