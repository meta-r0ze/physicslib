import PMFlavor.Values
import PMTransport.Values

/-!
# The flavour measurement pulls (moved from the PMFlavor comparison leaf)

The flavour values come from `PMFlavor.Values` (`vus`, `vcb`, `vub`, `pmnsSin2`, `q2`).
The conditional serial rate ratios come from `PMTransport.Values`. The direct measurements
come from PDG 2024 / NuFIT 6.0 (PMNS: normal ordering, IC19 without SK-atm; with SK-atm
`θ₂₃` is in the lower octant, `0.470`, and the model value `0.575` is `6σ` above it). (`vub`/`vcb` carry the convention's names; PMFlavor REVIEW item 0.)
-/

noncomputable section
namespace E8PConstants.FlavourPulls

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

theorem solar_pull : |(PMFlavor.Values.pmnsSin2 0 - 0.307) / 0.012| < 0.2 := by
  have h := PMFlavor.Values.pmnsSin2_bounds 0
  simp only [Matrix.cons_val_zero] at h
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith [h.1]
  · rw [div_lt_iff₀ (by norm_num)]; linarith [h.2]

theorem atmos_pull : 1.14 < (PMFlavor.Values.pmnsSin2 1 - 0.561) / 0.012 ∧
    (PMFlavor.Values.pmnsSin2 1 - 0.561) / 0.012 < 1.16 := by
  have h := PMFlavor.Values.pmnsSin2_bounds 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith [h.1]
  · rw [div_lt_iff₀ (by norm_num)]; linarith [h.2]

theorem reactor_pull : |(PMFlavor.Values.pmnsSin2 2 - 0.02195) / 0.00058| < 0.11 := by
  have h := PMFlavor.Values.pmnsSin2_bounds 2
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith [h.1]
  · rw [div_lt_iff₀ (by norm_num)]; linarith [h.2]

/-- Measured first-row sum `0.9984 ± 0.0007` against the dressed (`q² = 515/516`) and undressed
(`1`) first row. This is a benchmark comparison, not an input to any derivation. -/
theorem first_row_deficit_test :
    |PMFlavor.Values.q2 - 0.9984| / 0.0007 < 0.49 ∧ 2.28 < |(1 : ℝ) - 0.9984| / 0.0007 := by
  rw [PMFlavor.Values.q2_eq]
  constructor
  · rw [abs_of_neg (by norm_num)]; norm_num
  · rw [abs_of_pos (by norm_num)]; norm_num

/-- Comparison only. Both equal-normalization serial rates exceed the
upper end of the first-row wall-leakage diagnostic in the Flavor review.
The diagnostic uses the measured first-row deficit and its stated readout. -/
theorem serial_rate_first_row_comparison :
    (0.12 : ℝ) < PMTransport.Values.longSerialR ∧
    (0.12 : ℝ) < PMTransport.Values.shortSerialR := by
  rw [PMTransport.Values.longSerialR_eq, PMTransport.Values.shortSerialR_eq]
  norm_num

end E8PConstants.FlavourPulls
