import PMAction.RunningCoefficients
import PMConstants.ReadoutScales
import PMConstants.StrongRunning
import PMConstants.BetaUniversality

/-!
# Paper III's running coefficients come from Paper II

The one-loop coefficients used in Paper III's running tests are the values of
`PMAction.RunningCoefficients.b0`, which derives them from the spin decomposition.

* `readout_scales_coefficient`: `ReadoutScales.implied` uses `23/(6π) = b₀(SU(3), 5)/(2π)`.
* `threshold_coefficients`: `StrongRunning.invThreshold` uses `b₀(SU(3), 5)` and `b₀(SU(3), 4)`, and
  `invThree` uses `b₀(SU(3), 3) = 9`.
* `gauge_coefficient`: `BetaUniversality.gaugeCoeff` is the gauge part `spinTerm 2 · C_A`.
-/

namespace PMConstants.RunningLinks
open PMAction.RunningCoefficients

theorem readout_scales_coefficient :
    ((b0 3 5 0 : ℚ) : ℝ) / (2 * Real.pi) = 23 / (6 * Real.pi) := by
  rw [qcd_values.2.2.1]; push_cast; field_simp; ring

theorem threshold_coefficients :
    ((b0 3 5 0 : ℚ) : ℝ) = 11 - 2 * 5 / 3 ∧ ((b0 3 4 0 : ℚ) : ℝ) = 11 - 2 * 4 / 3 ∧
      ((b0 3 3 0 : ℚ) : ℝ) = 9 := by
  obtain ⟨h3, h4, h5, -⟩ := qcd_values
  rw [h3, h4, h5]; norm_num

theorem gauge_coefficient (cA : ℚ) : BetaUniversality.gaugeCoeff cA = spinTerm 2 * cA := by
  rw [gauge_part]; rfl

end PMConstants.RunningLinks
