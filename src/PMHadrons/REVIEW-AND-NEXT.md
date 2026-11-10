# PMHadrons — open work

Only work that remains, in priority order. Checked results are in
[`OVERVIEW.md`](OVERVIEW.md); **declared model inputs** (meson cell counts and residuals, the
triangle-loop normalization, bound-state values, the `Nucleon` protocol assignment, and the
decay-constant placeholders below) are terminal and recorded there, not here. The `fK`/`fπ`
tension is recorded in `e8p` (`f_k_mev` ≈ 3.8σ).

## 1. Substrate axial current and the current-to-hadron overlap — construction, large

This is the one big open item at the hadron level; the others below are separate research.

`fπ` and `fK` are **not** scales but matrix elements of the axial current:
`⟨0|A_μ^a|π^b(p)⟩ = i f_π p_μ δ^{ab}` (and likewise for `K`). The current formulas
`fπ = v/(Δ²+Δ−χ) = v/1890` and `fK = v/(Δ²−ν²) = v/1593` are **assigned placeholders** (`M`):
their denominators are chosen, not derived, and no cost selects a cell count (so the "one rule"
framing is retired — two points admit infinitely many rules). GMOR was tested with the derived PM
masses, `fK²/fπ² = [(m_s+m̂)/(2m̂)]·(m_π²/m_K²)`, and gives ≈ 1.08 vs the measured 1.193, so it
does not rescue the ratio either.

**Tasks.**
1. Define the substrate **axial current** from the existing chirality structures
   (`ChiralityConvention`, `PMConstants.CarrierRegisterChirality`, the weak current
   `PMHadrons.WeakTransition` / `PMElementaryParticles.CarrierTransitionOperator`).
2. Take the pion/kaon composite cohorts (`CompositeStates`) and compute the vacuum-to-one-particle
   overlap `⟨0|A_μ|π⟩`, `⟨0|A_μ|K⟩`, giving `fπ`, `fK` and their ratio from one object.
3. Reuse the same overlap machinery for the two things it also blocks:
   - the nonleptonic `K⁺ → π⁺π⁰`, `π⁺π⁺π⁻` amplitudes (`⟨ππ|T|K⁺⟩`; `.blocked` in
     `ParticleChannels`), currently a supplied `BoundStateMatrixElement.value`
     (`CompositeTransition`, `CompositePhaseSpace`, `HadronicMatrixElement`, `BoundStateOverlap`);
   - the `K_ℓ3` form factor `f₊(t)` (the leading-order `K_ℓ3` rate is in `KaonSemileptonic`,
     labelled "E8 leading order, ~10%").

**Closes when** the axial-current overlap is computed from a substrate wavefunction. Until then
`fπ`/`fK` stay declared model inputs.

## 2. Meson cell counts and the nucleon/meson base — research

Each meson is `n·α⁻¹ + residual`, with `n = χ` (pions) and `n = σ+χ` (kaons)
(`pion0_cells` … `kaonPlus_cells`); the nucleons use base `Δ²`, and `m_p/α⁻¹ ≈ 13.4` is not a
whole number. This is the *same* missing-cost problem as the decay-constant denominators: a
discrete cell count with no selecting cost.

**Tasks.** (a) a rule giving both `n` values — one candidate is `n = χ + σ·N_s` (`N_s` = number
of strange constituents), but it is an ansatz, so it is not committed; (b) a mass form covering
`Δ²` and whole cell budgets. Stop if no cost functional is supplied.

## Not work

The continuum neutron comparison (`NeutronRate`) is kept as a labelled cross-check, not an E8
assumption; the E8-native route (`NeutronPrediction`) is the headline. No action.
