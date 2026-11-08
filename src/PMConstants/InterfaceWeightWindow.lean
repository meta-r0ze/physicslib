import PMConstants.InterfaceCorrection
import PMConstants.CertifiedConstants

/-! **Effective interface weight from the Z-anchor window.**

For a constant effective spectral weight `N`,

```
Δr(N) = αN/(1 + αN).
```

The Z-anchor window `0.0349 < Δr < 0.0353` selects exactly `N = 5`.  This is the
first substrate-facing clue: the response must have effective weight `σ = 5`, not
the unweighted 24-root sum.
-/

noncomputable section
namespace PMConstants.InterfaceWeightWindow

open PMConstants

/-- `Δr` for a constant effective spectral weight. -/
def deltaRWeight (N : ℕ) : ℝ :=
  (CertifiedConstants.α * N) / (1 + CertifiedConstants.α * N)

theorem weight_five_in_window :
    0.0349 < deltaRWeight 5 ∧ deltaRWeight 5 < 0.0353 := by
  have ha := CertifiedConstants.alpha_bounds
  have hα : (0 : ℝ) < CertifiedConstants.α := by linarith [ha.1]
  have hK : (0 : ℝ) < 1 + CertifiedConstants.α * 5 := by positivity
  norm_num [deltaRWeight]
  constructor
  · rw [lt_div_iff₀ hK]
    nlinarith [ha.1]
  · rw [div_lt_iff₀ hK]
    nlinarith [ha.2]

/-- The window selects the effective weight `5`. -/
theorem weight_window (N : ℕ) :
    (0.0349 < deltaRWeight N ∧ deltaRWeight N < 0.0353) ↔ N = 5 := by
  have ha := CertifiedConstants.alpha_bounds
  have hα : (0 : ℝ) < CertifiedConstants.α := by linarith [ha.1]
  constructor
  · rintro ⟨h1, h2⟩
    have hK : (0 : ℝ) < 1 + CertifiedConstants.α * N := by positivity
    have h1' : 0.0349 * (1 + CertifiedConstants.α * N) < CertifiedConstants.α * N := by
      unfold deltaRWeight at h1
      rwa [lt_div_iff₀ hK] at h1
    have h2' : CertifiedConstants.α * N < 0.0353 * (1 + CertifiedConstants.α * N) := by
      unfold deltaRWeight at h2
      rwa [div_lt_iff₀ hK] at h2
    have hN1 : (4.9 : ℝ) < N := by nlinarith [ha.1, h1']
    have hN2 : (N : ℝ) < 5.1 := by nlinarith [ha.2, h2']
    have hN1' : 4 < N := by exact_mod_cast (by linarith : (4 : ℝ) < N)
    have hN2' : N < 6 := by exact_mod_cast (by linarith : (N : ℝ) < 6)
    omega
  · rintro rfl
    exact weight_five_in_window

theorem weight_four_low : deltaRWeight 4 < 0.0349 := by
  have ha := CertifiedConstants.alpha_bounds
  have hα : (0 : ℝ) < CertifiedConstants.α := by linarith [ha.1]
  have hK : (0 : ℝ) < 1 + CertifiedConstants.α * 4 := by positivity
  norm_num [deltaRWeight]
  rw [div_lt_iff₀ hK]
  nlinarith [ha.2]

theorem weight_six_high : 0.0353 < deltaRWeight 6 := by
  have ha := CertifiedConstants.alpha_bounds
  have hα : (0 : ℝ) < CertifiedConstants.α := by linarith [ha.1]
  have hK : (0 : ℝ) < 1 + CertifiedConstants.α * 6 := by positivity
  norm_num [deltaRWeight]
  rw [lt_div_iff₀ hK]
  nlinarith [ha.1]

/-- The selected effective weight is the embedding dimension `σ = 5`. -/
theorem effective_weight_eq_sigma : (5 : ℕ) = PMSubstrate.E8Values.sigma := by
  rw [PMSubstrate.E8Values.sigma_eq]

end PMConstants.InterfaceWeightWindow
