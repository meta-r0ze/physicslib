# PMHadrons — open work

Only work that remains, in priority order. Checked results are in
[`OVERVIEW.md`](OVERVIEW.md); **declared model inputs** (meson cell counts and residuals, the
triangle-loop normalization, bound-state values, the `Nucleon` protocol assignment) are terminal
and recorded there, not here. The `fK`/`fπ` tension is now recorded in `e8p` (`f_k_mev` ≈ 3.8σ).

## 1. One rule for `fK` and `fπ` — research

Their denominators have different shapes (`Δ²−ν²` vs `Δ²+Δ−χ`); `fK = v/1593`,
`fπ = v/1890`.

**Task.** Find a single rule that yields both and lands inside the FLAG 2024 lattice band
(`fK = 155.7(3)`, `fπ = 130.2(8)` MeV). Do **not** search integer combinations for a better fit
(look-elsewhere). If no rule appears, `fK` stays a declared model input.

## 2. Meson cell counts and the nucleon/meson base — research

Each meson is `n·α⁻¹ + residual`, with `n = χ` (pions) and `n = σ+χ` (kaons)
(`pion0_cells` … `kaonPlus_cells`); the nucleons use base `Δ²`, and `m_p/α⁻¹ ≈ 13.4` is not a
whole number.

**Tasks.** (a) a rule giving both `n` values — one candidate is `n = χ + σ·N_s` (`N_s` = number
of strange constituents), but it is an ansatz with no selecting cost, so it is not committed;
(b) a mass form covering `Δ²` and whole cell budgets. Stop if no cost functional is supplied.

## 3. Bound-state wavefunction — large, nonperturbative

Blocks the nonleptonic kaon channels `K⁺ → π⁺π⁰`, `π⁺π⁺π⁻` (`.blocked` in `ParticleChannels`)
and, at precision level, the `K_ℓ3` form factor `f₊(t)` (the leading-order `K_ℓ3` rate is in
`KaonSemileptonic`, labelled "E8 leading order, ~10%"). The structure exists
(`CompositeTransition`, `CompositePhaseSpace`, `HadronicMatrixElement`, `BoundStateOverlap`);
the amplitude is a supplied `BoundStateMatrixElement.value`.

**Task.** Compute the constituent-cohort overlap from a substrate bound-state wavefunction.

## Not work

The continuum neutron comparison (`NeutronRate`) is kept as a labelled cross-check, not an E8
assumption; the E8-native route (`NeutronPrediction`) is the headline. No action.
