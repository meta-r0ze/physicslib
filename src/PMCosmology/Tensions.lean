import PMCosmology.Scaling
import PMSubstrate.Impedance

/-!
# The tension arithmetic, certified in Lean

Paper VI quotes several numbers that `check_load_consistency.py` computes in
floating point but only partly certifies. This module certifies the remaining
parametric ones given the frozen inputs and Paper I's `α⁻¹` bounds:

* `hubbleInputSigma_exact` / `_bounds` — the early-rate `0.5` propagates to
  `(1/2)·L = 1491/2752 ∈ (0.5417, 0.5418)` (paper `0.541787791…`).
* `s8InputSigma_exact` / `_bounds` — the clustering `0.013` propagates to
  `(13/1000)/L = 2236/186375 ∈ (0.011997, 0.011998)` (paper `0.011997317…`).
* `omegaRatio_bounds` — the corrected dark count
  `248/(3ν(1−χ/Δ+α)) = 248/(48(1−2/43+α))` is in `(5.3775, 5.3776)`
  (paper `5.377543123…`), using `PMSubstrate.geometricIndex_bounds`.

The inputs (`0.5`, `0.013`, `5.36`) and the response/dark-count rules remain
model inputs; only the arithmetic is certified.
-/

noncomputable section
namespace PMCosmology.Tensions
open PMCosmology

/-- Exact propagated early-rate uncertainty `(1/2)·L`. -/
theorem hubbleInputSigma_exact : (1 / 2 : ℝ) * loadFactor = 1491 / 2752 := by
  norm_num [loadFactor]

/-- Certified enclosure `0.5417 < (1/2)·L < 0.5418`. -/
theorem hubbleInputSigma_bounds :
    (0.5417 : ℝ) < (1 / 2 : ℝ) * loadFactor ∧
      (1 / 2 : ℝ) * loadFactor < 0.5418 := by
  rw [hubbleInputSigma_exact]
  exact ⟨by norm_num, by norm_num⟩

/-- Exact propagated clustering uncertainty `(13/1000)/L`. -/
theorem s8InputSigma_exact : ((13 : ℝ) / 1000) / loadFactor = 2236 / 186375 := by
  norm_num [loadFactor]

/-- Certified enclosure `0.011997 < (13/1000)/L < 0.011998`. -/
theorem s8InputSigma_bounds :
    (0.011997 : ℝ) < ((13 : ℝ) / 1000) / loadFactor ∧
      ((13 : ℝ) / 1000) / loadFactor < 0.011998 := by
  rw [s8InputSigma_exact]
  exact ⟨by norm_num, by norm_num⟩

/-- The corrected dark count `248/(3ν(1−χ/Δ+α))` with `α = 1/α⁻¹`. -/
def omegaRatio : ℝ := 248 / (48 * (1 - 2 / 43 + 1 / PMSubstrate.geometricIndex))

/-- Certified enclosure `5.3775 < OmegaRatio < 5.3776`. -/
theorem omegaRatio_bounds : (5.3775 : ℝ) < omegaRatio ∧ omegaRatio < 5.3776 := by
  have hs : (137.0359992 : ℝ) < PMSubstrate.geometricIndex ∧
      PMSubstrate.geometricIndex < 137.0359993 := by
    have h := PMSubstrate.geometricIndex_bounds; constructor <;> linarith [h.1, h.2]
  have hs0 : (0 : ℝ) < PMSubstrate.geometricIndex := by linarith [hs.1]
  have hu : 1 / PMSubstrate.geometricIndex < 1 / 137.0359992 :=
    one_div_lt_one_div_of_lt (by norm_num) hs.1
  have hl : 1 / 137.0359993 < 1 / PMSubstrate.geometricIndex :=
    one_div_lt_one_div_of_lt hs0 hs.2
  have hx0 : (0 : ℝ) < 1 / PMSubstrate.geometricIndex := by positivity
  have hD : (0 : ℝ) < 48 * (1 - 2 / 43 + 1 / PMSubstrate.geometricIndex) := by nlinarith
  unfold omegaRatio
  constructor
  · rw [lt_div_iff₀ hD]
    nlinarith [hu, hl, hx0]
  · rw [div_lt_iff₀ hD]
    nlinarith [hu, hl, hx0]

end PMCosmology.Tensions
