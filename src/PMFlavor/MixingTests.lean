import PMFlavor.CKM

/-!
# Which mixing forms the data constrain

Paper IV's mixing forms evaluate E8 invariants; the open question is which construction produces
each. This module records which integers the measurements fix within each form's natural family,
so an E8 construction has a definite target. Data: PDG 2024 `|V_us| = 0.22431 ± 0.00085`,
`|V_ub| = 0.00382 ± 0.0002` (the CKM values of `E8PConstants.FlavourPulls`).

* `cabibbo_count_unique`: among `π/n`, only `n = 14 = ν − χ` lies within `3σ` of `|V_us|`
  (`c₁₃` differs from one by `10⁻⁵`, far below the error).
* `vub_count_unique`: among `1/(m Z_geo)`, only `m = 2 = χ` lies within `3σ` of `|V_ub|`; the
  boundary `π` in `1/(χ Z_geo + π)` is a `1%` correction, below the `5%` error.
* With `PMFlavor.ReactorConductance.channel_count_unique` (`n = 3` in `n/Z_geo` for the PMNS
  reactor angle), and `1/(nφ)` for the solar angle (only `n = 2` within `2σ`), four of the seven
  forms have a data-fixed integer.
* Not fixed at present precision (checked numerically, `2σ`): the `|V_cb|` denominator
  `Z_geo − nπ` (`n = 2…5`), the atmospheric `(1 + π/n)/2` (`n = 15…37`), and `δ = arctan(n/2)`
  (`n = 4…6`).
-/

noncomputable section
namespace PMFlavor.MixingTests
open PMFlavor.CKM

/-- **Cabibbo: only `π/14`.** -/
theorem cabibbo_count_unique (n : ℕ) (hn : 0 < n) :
    |(Real.pi / n - 0.22431) / 0.00085| < 3 ↔ n = 14 := by
  have hp := Real.pi_gt_d2
  have hp' := Real.pi_lt_d2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro h
    rw [abs_lt] at h
    obtain ⟨h1, h2⟩ := h
    rw [lt_div_iff₀ (by norm_num)] at h1
    rw [div_lt_iff₀ (by norm_num)] at h2
    have e1 : Real.pi < (0.22431 + 3 * 0.00085) * n := (div_lt_iff₀ hnR).1 (by linarith)
    have e2 : (0.22431 - 3 * 0.00085) * n < Real.pi := (lt_div_iff₀ hnR).1 (by linarith)
    have u : (n : ℝ) < 15 := by nlinarith
    have l : (13 : ℝ) < n := by nlinarith
    have u' : n < 15 := by exact_mod_cast u
    have l' : 13 < n := by exact_mod_cast l
    omega
  · rintro rfl
    have q1 : Real.pi / 14 < 0.225 := by rw [div_lt_iff₀ (by norm_num)]; linarith
    have q2 : 0.2242 < Real.pi / 14 := by rw [lt_div_iff₀ (by norm_num)]; linarith
    push_cast
    rw [abs_lt]; constructor
    · rw [lt_div_iff₀ (by norm_num)]; linarith
    · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- **`|V_ub|`: only `1/(2 Z_geo)`.** -/
theorem vub_count_unique (m : ℕ) (hm : 0 < m) :
    |(1 / (m * αinv) - 0.00382) / 0.0002| < 3 ↔ m = 2 := by
  have ha := ai_bounds
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : 0 < (m : ℝ) * αinv := mul_pos hmR (by linarith)
  constructor
  · intro h
    rw [abs_lt] at h
    obtain ⟨h1, h2⟩ := h
    rw [lt_div_iff₀ (by norm_num)] at h1
    rw [div_lt_iff₀ (by norm_num)] at h2
    have e1 : 1 < (0.00382 + 3 * 0.0002) * (m * αinv) := (div_lt_iff₀ hd).1 (by linarith)
    have e2 : (0.00382 - 3 * 0.0002) * (m * αinv) < 1 := (lt_div_iff₀ hd).1 (by linarith)
    have k1 : (m : ℝ) * αinv < m * 137.0359993 := mul_lt_mul_of_pos_left ha.2 hmR
    have k2 : (m : ℝ) * 137.0359992 < m * αinv := mul_lt_mul_of_pos_left ha.1 hmR
    have u : (m : ℝ) < 3 := by nlinarith
    have l : (1 : ℝ) < m := by nlinarith
    have u' : m < 3 := by exact_mod_cast u
    have l' : 1 < m := by exact_mod_cast l
    omega
  · rintro rfl
    have hd2 : (0 : ℝ) < 2 * αinv := by linarith
    have q1 : 1 / (2 * αinv) < 0.003649 := by rw [div_lt_iff₀ hd2]; nlinarith
    have q2 : 0.003648 < 1 / (2 * αinv) := by rw [lt_div_iff₀ hd2]; nlinarith
    push_cast
    rw [abs_lt]; constructor
    · rw [lt_div_iff₀ (by norm_num)]; linarith
    · rw [div_lt_iff₀ (by norm_num)]; linarith

end PMFlavor.MixingTests
