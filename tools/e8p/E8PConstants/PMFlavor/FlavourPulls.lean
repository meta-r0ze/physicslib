import PMFlavor.FlavourPulls
import PMFlavor.Values

/-!
# The flavour measurement pulls (moved from the PMFlavor comparison leaf)

The CKM values come from `PMFlavor.Values` (`vus`, `vcb`, `vub`) and the weak-mixing identity from
`PMFlavor.FlavourPulls`; the measured-pull comparisons against PDG 2024 / NuFIT 6.0 live here.
-/

noncomputable section
namespace E8PConstants.FlavourPulls
open PMSubstrate PMFlavor PMFlavor.FlavourPulls

theorem vus_pull : |(PMFlavor.Values.vus - 0.22431) / 0.00085| < 0.2 := by
  have hs := PMFlavor.Values.s12_bounds
  have hc := PMFlavor.Values.c13_bounds
  have h1 : (0.2243978 : ℝ) < PMFlavor.Values.vus := by
    unfold PMFlavor.Values.vus; nlinarith [hs.1, hc.1]
  have h2 : PMFlavor.Values.vus < (0.2243995 : ℝ) := by
    unfold PMFlavor.Values.vus; nlinarith [hs.2, hc.2, hs.1]
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem vcb_pull : |(PMFlavor.Values.vcb - 0.0411) / 0.0012| < 0.2 := by
  have h := PMFlavor.CKM.vcb_bounds
  unfold PMFlavor.Values.vcb
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith [h.1]
  · rw [div_lt_iff₀ (by norm_num)]; linarith [h.2]

theorem vub_pull :
    -1.1 < (PMFlavor.Values.vub - 0.00382) / 0.0002 ∧
      (PMFlavor.Values.vub - 0.00382) / 0.0002 < -1.0 := by
  have h := PMFlavor.Values.s13_bounds
  unfold PMFlavor.Values.vub
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith [h.1]
  · rw [div_lt_iff₀ (by norm_num)]; linarith [h.2]

theorem solar_pull : |(1 / (2 * φ) - 0.304) / 0.012| < 0.5 := by
  have h := sqrt5_b
  have hd : 0 < 2 * φ := by unfold φ; positivity
  have q1 : 1 / (2 * φ) < 0.30902 := by rw [div_lt_iff₀ hd]; unfold φ; nlinarith
  have q2 : 0.30901 < 1 / (2 * φ) := by rw [lt_div_iff₀ hd]; unfold φ; nlinarith
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem atmos_pull : |((1 + Real.pi / (16 + 5)) / 2 - 0.574) / 0.016| < 0.1 := by
  have hp := pi_b
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem reactor_pull : |((5 - 2) / PMFlavor.CKM.αinv - 0.02225) / 0.00056| < 0.7 := by
  have hg := PMFlavor.CKM.ai_bounds
  have hd : 0 < PMFlavor.CKM.αinv := by linarith [hg.1]
  have q1 : (5 - 2 : ℝ) / PMFlavor.CKM.αinv < 0.0218921 := by
    rw [div_lt_iff₀ hd]; nlinarith [hg.1]
  have q2 : 0.0218920 < (5 - 2 : ℝ) / PMFlavor.CKM.αinv := by
    rw [lt_div_iff₀ hd]; nlinarith [hg.2]
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- Measured first-row sum `0.9984 ± 0.0007` against the two hypotheses. This is
a benchmark comparison, not an input to any derivation. -/
theorem first_row_deficit_test :
    |(1 - 1/516 : ℝ) - 0.9984| / 0.0007 < 0.49 ∧ 2.28 < |(1 : ℝ) - 0.9984| / 0.0007 := by
  constructor
  · rw [abs_of_pos (by norm_num)]; norm_num
  · rw [abs_of_pos (by norm_num)]; norm_num

end E8PConstants.FlavourPulls
