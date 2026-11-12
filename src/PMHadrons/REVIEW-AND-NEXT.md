# PMHadrons — open work

## 1. Decay margins — what the substrate number is, and what it matches — H

Each channel has one substrate number on its rate. Read from the substrate side, then matched to
the SM factors it lines up with (comparison, floating point, outside Lean):

| channel | substrate factor on the rate | SM bundle it matches | match |
|---|---|---|---|
| π⁺ → μ⁺ν | `(Δ+ν+σ)/(Δ+ν+σ+χ) = 32/33` (`E8Margin.pionMargin`) | `|V_ud|²·S_EW`, `S_EW = 1 + (2α/π) ln(m_Z/m_p)` | `0.96975` with E8 `|V_ud|`, `α`, `m_p`, uncorrected `m_Z` (6×10⁻⁵); `0.96831` with measured `|V_ud|` (0.14%) |
| n → p e ν̄ | `Δ/(Δ−χ) = 43/41` (`neutronMarginFactor`, applied as lifetime × 41/43) | `|V_ud|²·(1+3g_A²)/(1+3·(5/4)²)·⟨F_Coulomb⟩·(1+RC)` relative to the spectral `1/(3P)` | `1.0468` against `1.0488` (0.2%) |
| K⁺ → μ⁺ν | none; `|V_us|² = (π/14)² c₁₃²` written explicitly | `|V_us|²·S_EW` | the `S_EW` part has no substrate factor; the kaon's +3.5% is that plus the `f_K` tension |

So the two margins pointing in opposite directions is not a contradiction: each is one substrate
number standing for a different SM bundle. The pion's is dominated by `|V_ud|²` (down); the
neutron's by Coulomb attraction and the radiative correction (up). The K/π ratio
(`KaonPionRatio`) confirms the pion bundle contains `|V_ud|²`.

Open, from the substrate side:

- **41/43 already has a substrate reading: the Governor.** `PMAtoms.PersistenceComplex` proves
  `phaseMargin_eq_one_add_governor` (`41/43 = 1 + governorTerm = 1 − χ/Δ`) and
  `neutronMarginFactor_eq_phaseFraction`: it is the fraction of the `Δ` clock phases that survive a
  boundary gap `χ` (`survivingPhases`, `Δ−χ = 41`). The same Governor rule is the alpha
  suppression, `alphaPhaseFraction gap = 1 − gap/Δ`, and there it **multiplies the rate**
  (`AlphaPersistence`: `alphaCapacity · alphaPhaseFraction`), as `E8Margin.phaseCorrected` does.
  The neutron divides its rate by it (lifetime × 41/43). So the reading is settled; the neutron is
  the one use that applies it the other way, and it is the use that matches 878 s.
- **32/33 has no reading yet.** Why the two-body meson channel loses `χ` over the
  `Δ+ν+σ = 64` slots.
- **`E8Margin` disagrees with the neutron's use.** `phaseCorrected w = (41/43)·w` and
  `phaseCorrectedLifetime τ = τ/(41/43)` lower the rate; `neutronLifetimeCorrected = (41/43)·τ`
  raises it. One reading has to be chosen and the other definition changed.
- **The kaon channel's factor.** On the pion's pattern the kaon would carry `|V_us|²` times the
  substrate counterpart of `S_EW`; the substrate supplies `|V_us|²` but not that counterpart.
- The SM side's `g_A`: `NeutronRate.gA = σ/D = 5/4` against `1.2754`; on the spectral route `g_A`
  does not appear separately.

## 2. Beta cube rule — C/H

With the `3×3×3` cube only the lowest mode is open for any cutoff in `[6−3√2, 6−2√2) m_e`, so
`τ_n` does not depend on `m_n − m_p` there; below `6−3√2 = 1.757 m_e` no mode opens (tritium,
C-14 would not decay). Nuclear beta decay needs a rule for the cube (`≥ 5×5×5` for tritium).

## 3. Canonical values — done

`PMHadrons.Values` exports the nucleon and meson masses, decay constants, the corrected
lifetimes, the K/π ratio, `neutronMarginFactor` and the Toll/Governor emission names, for
`PMAtoms` and `e8p`. e8p still cites the defining modules; re-point its hadron rows next.

`PMFlavor.Values` is the single source for `vud`, `vus`, `vub`, `vcb`, `q2`, `vudDressed`,
`jarlskog`, `jarlskogGeo` and their bounds. Pointed at it: `KaonWidth.vusE8` and
`PMElementaryParticles.CarrierAmplitude.vud` (now abbreviations), `KaonPionRatio`,
`PMCosmology.Primordial`, and the e8p CKM rows. `PMFlavor.FlavourPulls` no longer keeps its own
`αinv`/`s12`/`s13`/`vus`/`vcb` copies. `PMCosmology.Tensions` takes `α⁻¹` from
`PMSubstrate.geometricIndex` instead of `PMFlavor.CKM`. `NeutronPrediction.neutronMarginFactor` is
`PMSubstrate.E8Margin.phaseMargin`.
