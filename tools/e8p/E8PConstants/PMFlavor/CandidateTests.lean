import PMFlavor.VubSeriesPath
import PMFlavor.HalfTurnMixing
import PMFlavor.TransferAmplitude
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Candidate mixing formulas against measurement (comparison leaf)

Moved out of the PMFlavor derivation modules: no derivation imports this file. Each theorem compares a
candidate's value with a frozen measured number; none selects a construction.

* `quark_share_fits`, `rotation_excluded`: `s₁₂ = π/14` against `0.22453 ± 0.00085` (dressing removed);
  `sin(π/14)` is more than `2σ` low (`HalfTurnMixing`).
* `lepton_share_fits`: `π/10` against JUNO's `0.3092 ± 0.0087`.
* `vcb_not_two_leg`: no two-leg passive path with boundary count `|k| ≤ 6` reaches `|V_cb|`.
* `frame_share_excluded`, `direction_shares_fit`: shares of `1 − η` against the first-row sum; the
  derived `515/516` (`DressingEvent`) does not rest on them.
* `promo_rules_excluded`: the three amplitude rules of `PMFlavor.TransferAmplitude` give
  `|promotion/jump| = 1`, `≈ 1.98`, `≈ 23.7`; each is more than `13σ` from `|V_cb|/|V_ub| = 10.76 ± 0.645`.
-/

noncomputable section
namespace E8PConstants.CandidateTests
open PMFlavor

theorem quark_share_fits : |Real.pi / 14 - 0.22453| / 0.00085 < 1 := by
  have h1 := Real.pi_gt_d4; have h2 := Real.pi_lt_d4
  rw [div_lt_one (by norm_num), abs_lt]; constructor <;> linarith

theorem rotation_excluded : Real.sin (Real.pi / 14) < 0.22453 - 2 * 0.00085 := by
  have h1 := Real.pi_gt_d4; have h2 := Real.pi_lt_d4
  set x := Real.pi / 14 with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hlo : (0.22439 : ℝ) ≤ x := by rw [hx]; linarith
  have hhi : x ≤ (0.22440 : ℝ) := by rw [hx]; linarith
  have hb := Real.sin_bound (x := x) (by rw [abs_of_pos hx0]; linarith)
  rw [abs_of_pos hx0] at hb
  have hb' := (abs_le.mp hb).2
  have h3 : (0.22439 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hlo 3
  have h5 : x ^ 5 ≤ (0.22440 : ℝ) ^ 5 := pow_le_pow_left₀ hx0.le hhi 5
  norm_num at h3 h5 ⊢
  linarith

theorem lepton_share_fits : |Real.pi / 10 - 0.3092| / 0.0087 < 1 := by
  have h1 := Real.pi_gt_d4; have h2 := Real.pi_lt_d4
  rw [div_lt_one (by norm_num), abs_lt]; constructor <;> linarith

/-- **`|V_cb|` is not a two-leg passive path.** Two legs with any boundary count `|k| ≤ 6` give at
most `1/(2Z − 6π) ≈ 0.0039`, far below `|V_cb| = 0.0411 ± 0.0012`. So the `c`-side node-crossing
mixing carries a drive of order `π + χ` that the `|V_ub|` path does not: the `s`/`c` parity
asymmetry (`ExchangeChirality`) shows up as a factor `≈ 10` in the drive, not only in the path. -/
theorem vcb_not_two_leg (k : ℤ) (hk : -6 ≤ k) :
    1 / (2 * CKM.αinv + k * Real.pi) < 0.0411 - 3 * 0.0012 := by
  have ha := CKM.ai_bounds
  have hp1 := Real.pi_gt_d4; have hp2 := Real.pi_lt_d4
  have hk' : (-6 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : -6 * Real.pi ≤ k * Real.pi := by nlinarith
  have hden : 255 < 2 * CKM.αinv + k * Real.pi := by linarith
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-! ## Which reference-exclusion share the first row allows (moved from `PMFlavor.CabibboDressing`)

Against the measured first-row sum `0.9984 ± 0.0007` (the benchmark of
`E8PConstants.FlavourPulls.first_row_deficit_test`), the shares of the reference exclusion
`1 − η = 1/172`: -/

/-- The whole frame's exclusion `1/172` is excluded (more than `6σ`), and so is one row's
`1/43`. -/
theorem frame_share_excluded :
    6 < |(1 - 1/172 : ℝ) - 0.9984| / 0.0007 ∧ 6 < |(1 - 1/43 : ℝ) - 0.9984| / 0.0007 := by
  constructor <;> (rw [abs_of_neg (by norm_num)]; norm_num)

/-- Both per-direction shares fit within `1σ`: over all `D` directions (`1/688`) and over the
`D − 1` spatial ones (`1/516`). The data do not separate them. -/
theorem direction_shares_fit :
    |(1 - 1/688 : ℝ) - 0.9984| / 0.0007 < 1 ∧ |(1 - 1/516 : ℝ) - 0.9984| / 0.0007 < 1 := by
  constructor
  · rw [abs_of_pos (by norm_num)]; norm_num
  · rw [abs_of_neg (by norm_num)]; norm_num

/-- **None of the library's node-crossing rules gives the measured `|V_cb|/|V_ub|`.** -/
theorem promo_rules_excluded :
    15 < |PMFlavor.TransferAmplitude.promoA / PMFlavor.TransferAmplitude.jump - 10.76| / 0.645 ∧
      13 < |PMFlavor.TransferAmplitude.promoB / PMFlavor.TransferAmplitude.jump - 10.76| / 0.645 ∧
      19 < |PMFlavor.TransferAmplitude.promoC / PMFlavor.TransferAmplitude.jump - 10.76| / 0.645 := by
  have hA := PMFlavor.TransferAmplitude.promoA_ratio
  have hB := PMFlavor.TransferAmplitude.promoB_ratio
  have hC := PMFlavor.TransferAmplitude.promoC_ratio_sq
  have hj : 0 < PMFlavor.TransferAmplitude.jump := by
    rw [PMFlavor.TransferAmplitude.jump_eq]
    have := Real.pi_pos; have := PMFlavor.TransferAmplitude.αinv_pos; positivity
  have hc : 0 < PMFlavor.TransferAmplitude.promoC :=
    Real.sqrt_pos.2 (by have := PMFlavor.TransferAmplitude.αinv_pos; positivity)
  have hCpos : 0 < PMFlavor.TransferAmplitude.promoC / PMFlavor.TransferAmplitude.jump :=
    div_pos hc hj
  have hC' : 23.6 < PMFlavor.TransferAmplitude.promoC / PMFlavor.TransferAmplitude.jump := by
    nlinarith [hC.1]
  refine ⟨?_, ?_, ?_⟩
  · rw [hA, lt_div_iff₀ (by norm_num), abs_of_neg (by norm_num)]; norm_num
  · rw [lt_div_iff₀ (by norm_num), abs_of_neg (by linarith [hB.2])]; linarith [hB.2]
  · rw [lt_div_iff₀ (by norm_num), abs_of_pos (by linarith)]; linarith

end E8PConstants.CandidateTests
