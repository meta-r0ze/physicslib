import PMFlavor.FlavourPulls

/-!
# The flavour measurement pulls (moved from the PMFlavor comparison leaf)

The CKM/PMNS value formulas (`vus`, `vcb`, `s13`, ...) and the weak-mixing identity stay in
`PMFlavor.FlavourPulls`; the measured-pull comparisons against PDG 2024 / NuFIT 6.0 live here.
-/

noncomputable section
namespace E8PConstants.FlavourPulls
open PMSubstrate PMFlavor PMFlavor.FlavourPulls

theorem vus_pull : |(vus - 0.22431) / 0.00085| < 0.2 := by
  have hp := pi_b; have h13 := s13_b
  have hc : (0.99999349 : ℝ) < Real.sqrt (1 - s13 ^ 2) ∧ Real.sqrt (1 - s13 ^ 2) ≤ 1 := by
    constructor
    · rw [Real.lt_sqrt (by norm_num)]; nlinarith
    · rw [Real.sqrt_le_one]; nlinarith
  have hs : (0.22439947 : ℝ) < s12 ∧ s12 < 0.22439948 := by
    unfold s12; constructor <;> linarith
  unfold vus
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith

theorem vcb_pull : |(vcb - 0.0411) / 0.0012| < 0.2 := by
  have hp := pi_b; have hg := g_b
  have hd : 0 < αinv - 4 * Real.pi := by linarith
  unfold vcb
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num), lt_sub_iff_add_lt, lt_div_iff₀ hd]; nlinarith
  · rw [div_lt_iff₀ (by norm_num), sub_lt_iff_lt_add, div_lt_iff₀ hd]; nlinarith

theorem vub_pull : -1.1 < (s13 - 0.00382) / 0.0002 ∧ (s13 - 0.00382) / 0.0002 < -1.0 := by
  have h := s13_b
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

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

theorem reactor_pull : |((5 - 2) / αinv - 0.02225) / 0.00056| < 0.7 := by
  have hg := g_b
  have hd : 0 < αinv := by linarith
  have q1 : (5 - 2 : ℝ) / αinv < 0.0218921 := by rw [div_lt_iff₀ hd]; nlinarith
  have q2 : 0.0218920 < (5 - 2 : ℝ) / αinv := by rw [lt_div_iff₀ hd]; nlinarith
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- Measured first-row sum `0.9984 ± 0.0007` against the two hypotheses. This is
a benchmark comparison, not an input to any derivation. -/
theorem first_row_deficit_test :
    |(1 - 1/688 : ℝ) - 0.9984| / 0.0007 < 0.22 ∧ 2.28 < |(1 : ℝ) - 0.9984| / 0.0007 := by
  constructor
  · rw [abs_of_pos (by norm_num)]; norm_num
  · rw [abs_of_pos (by norm_num)]; norm_num

end E8PConstants.FlavourPulls
