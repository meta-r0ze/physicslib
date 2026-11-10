# PMHadrons — open work

Only work that remains, in priority order. Checked results are in
[`OVERVIEW.md`](OVERVIEW.md); **declared model inputs** (meson cell counts and residuals, the
triangle-loop normalization, bound-state values, the `Nucleon` protocol assignment) are terminal
and recorded there, not here.

## 1. Record `fK` (and `fπ`) in `e8p` — small

`fπ = v/(Δ²+Δ−χ) = v/1890` agrees with the FLAG 2024 lattice (`130.27` vs `130.2(8)` MeV).
`fK = v/(Δ²−ν²) = v/1593` is the weakest number at this level: `154.56` vs `155.7(3)` MeV
(≈ 3.8σ low), and `fK/fπ = 1890/1593 ≈ 1.1864` vs `1.1932(19)` (≈ 3.6σ). Neither is in the
catalog, so the tension is invisible to the audit.

**Task.** Add `f_pi_mev` / `f_k_mev` rows to `e8p` from
`PionWidth.pionDecayConstantMeV_bounds` / `KaonWidth.kaonDecayConstantMeV_bounds`, with FLAG
2024 references.

## 2. One rule for `fK` and `fπ` — research

Their denominators have different shapes (`Δ²−ν²` vs `Δ²+Δ−χ`).

**Task.** Find a single rule that yields both and lands inside the lattice band. Do **not**
search integer combinations for a better fit (look-elsewhere). If no rule appears, `fK` stays a
declared model input.

## 3. Meson cell counts and the nucleon/meson base — research

Each meson is `n·α⁻¹ + residual`, with `n = χ` (pions) and `n = σ+χ` (kaons)
(`pion0_cells` … `kaonPlus_cells`); the nucleons use base `Δ²`, and `m_p/α⁻¹ ≈ 13.4` is not a
whole number.

**Tasks.** (a) a rule giving both `n` values — one candidate is `n = χ + σ·N_s` (`N_s` = number
of strange constituents), but it is an ansatz with no selecting cost, so it is not committed;
(b) a mass form covering `Δ²` and whole cell budgets. Stop if no cost functional is supplied.

## 4. Bound-state wavefunction — large, nonperturbative

Blocks the nonleptonic kaon channels `K⁺ → π⁺π⁰`, `π⁺π⁺π⁻` (`.blocked` in `ParticleChannels`)
and, at precision level, the `K_ℓ3` form factor `f₊(t)`. The structure exists
(`CompositeTransition`, `CompositePhaseSpace`, `HadronicMatrixElement`, `BoundStateOverlap`);
the amplitude is a supplied `BoundStateMatrixElement.value`.

**Task.** Compute the constituent-cohort overlap from a substrate bound-state wavefunction.

## 5. Leading-order `K_ℓ3` channel — small

`K⁺ → π⁰ e⁺ν`, `π⁰ μ⁺ν` are `.blocked` but need no wavefunction at leading order: with
`f₊(0) = 1` and `m_ℓ → 0`, the width is
`G_F²|V_us|² m_K⁵·½·(phase(z)/4)/(192π³)`, `z = (m_π/m_K)²`, reusing `MassiveWidth.phase`
(the `λ^{3/2}` Dalitz integral is `phase(z)/4`); every factor is already E8 in this repo.

**Task.** Add `kaonL3Width` and move the two rows off `.blocked` to an "E8 leading order,
~10%" status. The remaining ~10% is item 4.

## Not work

The continuum neutron comparison (`NeutronRate`) is kept as a labelled cross-check, not an E8
assumption; the E8-native route (`NeutronPrediction`) is the headline. No action.
