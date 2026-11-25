import PMConstants.Values

/-! Comparisons of the VEV, scalar, and boundary-storage forms with
the frozen Fermi and gravity reference windows. -/

noncomputable section
namespace E8PConstants.VevWindow

open PMConstants VevCorrections ElectroweakE8 CertifiedConstants ElectroweakBounds
open VevAccounting VevBoundary GravityAccounting PMSubstrate.E8Values ScalarSector

/-- **Only divisors 3 and 4 fit.** -/
theorem divisor_window (k : ℕ) (hk : 0 < k) :
    (246.21957 < withDivisor k ∧ withDivisor k < 246.21971) ↔ k = 3 ∨ k = 4 := by
  have hv := V_bounds
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hden : (0 : ℝ) < 1 - Y / 3 := by norm_num [Y_val]
  unfold withDivisor
  rw [lt_div_iff₀ hden, div_lt_iff₀ hden]
  constructor
  · rintro ⟨h1, h2⟩
    have hr1 : (0.2324 : ℝ) < 1 / k := by
      by_contra hc; push Not at hc
      have : V * (1 - Y / k) ≥ V * (1 - Y * 0.2324) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        have : Y / k = Y * (1 / k) := by ring
        rw [this]; nlinarith [show (0 : ℝ) < Y by norm_num [Y_val]]
      norm_num [Y_val] at h2 this; nlinarith
    have hr2 : 1 / (k : ℝ) < 0.4286 := by
      by_contra hc; push Not at hc
      have : V * (1 - Y / k) ≤ V * (1 - Y * 0.4286) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        have : Y / k = Y * (1 / k) := by ring
        rw [this]; nlinarith [show (0 : ℝ) < Y by norm_num [Y_val]]
      norm_num [Y_val] at h1 this; nlinarith
    rw [lt_div_iff₀ hkpos] at hr1
    rw [div_lt_iff₀ hkpos] at hr2
    have a : 2 < k := by
      have : (2 : ℝ) < k := by linarith
      exact_mod_cast this
    have b : k < 5 := by
      have : (k : ℝ) < 5 := by nlinarith
      exact_mod_cast this
    omega
  · rintro (rfl | rfl) <;> norm_num [Y_val] <;> constructor <;> nlinarith [hv.1, hv.2]

/-- **The window pins the effective dimension.** -/
theorem dimension_window {Dp : ℝ} (hD : 0 < Dp)
    (h : 246.21957 < withDimension Dp ∧ withDimension Dp < 246.21971) :
    4.1584 < Dp ∧ Dp < 4.1599 := by
  have hv := V_bounds
  have hx := x_bounds
  have ha := alpha_bounds
  have h1x : (0 : ℝ) < 1 + x := by linarith
  unfold withDimension at h
  rw [lt_div_iff₀ h1x, div_lt_iff₀ h1x] at h
  obtain ⟨h1, h2⟩ := h
  have hq1 : 0.00175425 < α / Dp := by nlinarith
  have hq2 : α / Dp < 0.00175483 := by nlinarith
  rw [lt_div_iff₀ hD] at hq1
  rw [div_lt_iff₀ hD] at hq2
  constructor <;> nlinarith

/-- **Among `D + a/(bπ)` with `b ≤ 200`, only `a/b = 1/2`, i.e. `χ/(4π)`, fits.** -/
theorem boundary_unique (a b : ℕ) (hb : 0 < b) (hb2 : b ≤ 200) :
    (246.21957 < withDimension (4 + a / (b * Real.pi)) ∧
        withDimension (4 + a / (b * Real.pi)) < 246.21971) ↔ 2 * a = b := by
  have hp := pi_bounds
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hbp : (0 : ℝ) < b * Real.pi := by nlinarith
  constructor
  · intro h
    have hD : (0 : ℝ) < 4 + a / (b * Real.pi) := by positivity
    obtain ⟨d1, d2⟩ := dimension_window hD h
    have e1 : (0.1584 : ℝ) * (b * Real.pi) < a := by
      have := (lt_div_iff₀ hbp).mp (by linarith : (0.1584 : ℝ) < a / (b * Real.pi)); linarith
    have e2 : (a : ℝ) < 0.1599 * (b * Real.pi) := by
      have := (div_lt_iff₀ hbp).mp (by linarith : (a : ℝ) / (b * Real.pi) < 0.1599); linarith
    have i1 : (4976 : ℝ) * b < 10000 * a := by nlinarith
    have i2 : (10000 : ℝ) * a < 5024 * b := by nlinarith
    have j1 : 4976 * b < 10000 * a := by exact_mod_cast i1
    have j2 : 10000 * a < 5024 * b := by exact_mod_cast i2
    omega
  · intro hab
    have hab' : (a : ℝ) / (b * Real.pi) = 2 / (4 * Real.pi) := by
      have : (b : ℝ) = 2 * a := by exact_mod_cast hab.symm
      rw [this]; have : (a : ℝ) ≠ 0 := by
        intro h0; rw [h0] at this; linarith
      field_simp; ring
    have hv := V_bounds
    have hx := x_bounds
    have hdim : effectiveDimension = 4 + 2 / (4 * Real.pi) := by
      unfold effectiveDimension
      rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.chi_eq]
      norm_num
    unfold withDimension
    rw [hab', ← hdim]
    have : α / effectiveDimension = x := rfl
    rw [this, mul_div_assoc, div_self (by linarith), mul_one]
    constructor <;> linarith

/-- **Partial repairs are excluded by the Fermi window.** -/
theorem compound_excluded (n : ℕ) (hn : 2 ≤ n) : 246.21971 < V * (1 + x / n) ^ n / (1 + x) := by
  have hv := V_bounds
  have hx := x_bounds
  have hc := VevReadout.compound_lower x (by linarith) n hn
  have hpos : 0 < 1 + x := by linarith
  rw [lt_div_iff₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_left hc (by linarith : (0:ℝ) ≤ V)]

/-- **An unnormalized total reads `Y`: divisor `1`, excluded.** -/
theorem total_excluded : ¬ (246.21957 < withDivisor (1 : ℕ) ∧ withDivisor (1 : ℕ) < 246.21971) := by
  rw [divisor_window 1 (by norm_num)]; omega

/-- **The VEV with both readings.** -/
theorem vev_from_readout :
    246.21957 < withDivisor (3 : ℕ) ∧ withDivisor (3 : ℕ) < 246.21971 :=
  (divisor_window 3 (by norm_num)).mpr (Or.inl rfl)

/-- The Fermi window for `D_eff = 4 + r`. -/
def Fits (r : ℝ) : Prop := 246.21957 < withDimension (4 + r) ∧ withDimension (4 + r) < 246.21971

lemma excluded {r : ℝ} (a b : ℕ) (hr : r = (a : ℝ) / ((b : ℝ) * Real.pi)) (hb : 0 < b)
    (hb2 : b ≤ 200) (hne : 2 * a ≠ b) : ¬ Fits r := by
  rw [Fits, hr]; exact fun h => hne ((boundary_unique a b hb hb2).1 h)

theorem selected_fits : Fits (parallelClosures (chi : ℝ) (D : ℝ)) := by
  rw [Fits, show parallelClosures (chi : ℝ) (D : ℝ) = ((2 : ℕ) : ℝ) / (((4 : ℕ) : ℝ) * Real.pi) by
    simp only [parallelClosures, chi_eq, D_eq]; push_cast; ring]
  exact (boundary_unique 2 4 (by norm_num) (by norm_num)).2 (by norm_num)

theorem series_excluded : ¬ Fits (seriesClosures (chi : ℝ) (D : ℝ)) :=
  excluded 1 8 (by simp only [seriesClosures, chi_eq, D_eq]; push_cast; ring)
    (by norm_num) (by norm_num) (by norm_num)

theorem cycle_width_excluded : ¬ Fits (parallelClosures (chi : ℝ) (Delta : ℝ)) :=
  excluded 2 43 (by simp only [parallelClosures, chi_eq, Delta_eq]; push_cast; ring)
    (by norm_num) (by norm_num) (by norm_num)

theorem one_closure_excluded : ¬ Fits (parallelClosures 1 (D : ℝ)) :=
  excluded 1 4 (by simp only [parallelClosures, D_eq]; push_cast; ring)
    (by norm_num) (by norm_num) (by norm_num)

theorem sigma_excluded : ¬ Fits (parallelClosures (sigma : ℝ) (D : ℝ)) :=
  excluded 5 4 (by simp only [parallelClosures, sigma_eq, D_eq]; push_cast; ring)
    (by norm_num) (by norm_num) (by norm_num)

theorem nu_excluded : ¬ Fits (parallelClosures (nu : ℝ) (D : ℝ)) :=
  excluded 16 4 (by simp only [parallelClosures, nu_eq, D_eq]; push_cast; ring)
    (by norm_num) (by norm_num) (by norm_num)

theorem no_pi_excluded : ¬ Fits ((chi : ℝ) / (D : ℝ)) := by
  intro h
  rw [Fits, show (chi : ℝ) / (D : ℝ) = 1 / 2 by rw [chi_eq, D_eq]; norm_num] at h
  have := dimension_window (by norm_num) h
  norm_num at this

/-- **The noise divisor.** -/
theorem noise_divisor :
    (246.21957 < VevCorrections.withDivisor 3 ∧ VevCorrections.withDivisor 3 < 246.21971) ∧
      VevCorrections.Y ≠ 0 :=
  ⟨(divisor_window 3 (by norm_num)).mpr (Or.inl rfl), by
    rw [VevCorrections.Y_val]; norm_num⟩

theorem storage_window {s : ℝ}
    (h : 1.751770e-45 < (16 - s - α) * α ^ ((43 : ℝ) / 2) ∧
      (16 - s - α) * α ^ ((43 : ℝ) / 2) < 1.751849e-45) :
    0.6662 < s ∧ s < 0.6670 := by
  have ha := alpha_bounds
  have hA := attenuation_bounds
  have hApos : 0 < α ^ ((43 : ℝ) / 2) := by linarith [hA.1]
  constructor
  · by_contra hc; push Not at hc
    have : (16 - s - α) * α ^ ((43 : ℝ) / 2) ≥ (16 - 0.6662 - 0.007297352563) * 1.143021965e-46 := by
      have h1 : 16 - s - α ≥ 16 - 0.6662 - 0.007297352563 := by linarith [ha.2]
      nlinarith [hA.1]
    norm_num at this; linarith [h.2]
  · by_contra hc; push Not at hc
    have : (16 - s - α) * α ^ ((43 : ℝ) / 2) ≤ (16 - 0.6670 - 0.007297352562) * 1.143021969e-46 := by
      have h1 : 16 - s - α ≤ 16 - 0.6670 - 0.007297352562 := by linarith [ha.1]
      have h0 : 0 ≤ 16 - s - α ∨ 16 - s - α < 0 := le_or_gt 0 _
      rcases h0 with h0 | h0
      · nlinarith [hA.2]
      · nlinarith [hA.2]
    norm_num at this; linarith [h.1]

theorem chi_over_k (k : ℕ) : ((0.6662 : ℚ) < 2 / k ∧ 2 / (k : ℚ) < 0.6670) ↔ k = 3 := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k <;> revert h1 h2 <;> norm_num
    · rcases Nat.eq_or_lt_of_le hk with hk | hk
      · exact hk.symm
      · have hk4 : (4 : ℚ) ≤ k := by exact_mod_cast hk
        have : 2 / (k : ℚ) ≤ 1/2 := by
          rw [div_le_iff₀ (by linarith)]; linarith
        linarith
  · rintro rfl; norm_num

theorem payload_weighted_excluded : 2 * PMConstants.overhead / 3 < (0.6662 : ℝ) := by
  norm_num [PMConstants.overhead]

theorem fermi_window {GF : ℝ} (h : 1.1663782e-5 < GF ∧ GF < 1.1663794e-5) :
    246.21957 < Real.sqrt (1 / (Real.sqrt 2 * GF)) ∧
      Real.sqrt (1 / (Real.sqrt 2 * GF)) < 246.21971 := by
  have hs := PMConstants.JointConstants.sqrt_two_bounds
  have hd : 0 < Real.sqrt 2 * GF := by nlinarith [hs.1, h.1]
  constructor
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ hd]; nlinarith [hs.2, h.2]
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ hd]; nlinarith [hs.1, h.1]

theorem frame_inside {GF : ℝ} (h : 1.1663782e-5 < GF ∧ GF < 1.1663794e-5) :
    Real.sqrt (1 / (Real.sqrt 2 * GF)) - 0.00008 < vevWith 188 ∧
      vevWith 188 < Real.sqrt (1 / (Real.sqrt 2 * GF)) + 0.00008 := by
  have hw := fermi_window h
  have hv := vev_bounds
  rw [frame_is_paper]
  constructor <;> linarith [hw.1, hw.2, hv.1, hv.2]

theorem payload_outside {GF : ℝ} (h : 1.1663782e-5 < GF ∧ GF < 1.1663794e-5) :
    Real.sqrt (1 / (Real.sqrt 2 * GF)) < 246.2261 ∧ 246.2261 < vevWith (172 + 16 * PMConstants.overhead) := by
  have hw := fermi_window h
  have hv := vev_bounds
  refine ⟨by linarith [hw.2], ?_⟩
  unfold vevWith; norm_num [PMConstants.overhead]
  nlinarith [hv.1]

theorem footprint_outside {GF : ℝ} (h : 1.1663782e-5 < GF ∧ GF < 1.1663794e-5) :
    vevWith footprint < 245.876 ∧ 245.876 < Real.sqrt (1 / (Real.sqrt 2 * GF)) := by
  have hw := fermi_window h
  have hv := vev_bounds
  refine ⟨?_, by linarith [hw.1]⟩
  unfold vevWith; norm_num [footprint, PMConstants.overhead]
  nlinarith [hv.2]

theorem wire_share_excluded {GF s : ℝ} (h : 1.1663782e-5 < GF ∧ GF < 1.1663794e-5)
    (hs : 1/1000 ≤ s) :
    vevWith (188 + 5 * s) < Real.sqrt (1 / (Real.sqrt 2 * GF)) - 0.00008 := by
  have hw := fermi_window h
  have hv := vev_bounds
  have hpos : 0 < vev α electronGeV := by linarith [hv.1]
  unfold vevWith
  have e : (2 * 43^2 - (188 + 5 * s)) / 3510 = 1 - s / 702 := by ring
  rw [e]
  have : vev α electronGeV * (1 - s / 702) ≤ vev α electronGeV * (1 - (1/1000) / 702) := by
    apply mul_le_mul_of_nonneg_left _ hpos.le; linarith
  have h2 : vev α electronGeV * (1 - (1/1000) / 702) < 246.2196382 * (1 - (1/1000) / 702) := by
    apply mul_lt_mul_of_pos_right hv.2; norm_num
  linarith [hw.1]

theorem higgs_from_fermi {GF : ℝ} (h : 1.1663782e-5 < GF ∧ GF < 1.1663794e-5) :
    125.26 < Real.sqrt (higgsSq GF) ∧ Real.sqrt (higgsSq GF) < 125.28 := by
  have hs := JointConstants.sqrt_two_bounds
  have hd : 0 < Real.sqrt 2 * GF := by nlinarith [hs.1, h.1]
  have hlo : (125.26 : ℝ)^2 < higgsSq GF := by
    unfold higgsSq selfCoupling
    rw [PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.sigma_eq,
      PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.Delta_eq]
    rw [lt_div_iff₀ hd]; nlinarith [hs.2, h.2]
  have hhi : higgsSq GF < (125.28 : ℝ)^2 := by
    unfold higgsSq selfCoupling
    rw [PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.sigma_eq,
      PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.Delta_eq]
    rw [div_lt_iff₀ hd]; nlinarith [hs.1, h.1]
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; exact hlo
  · rw [Real.sqrt_lt' (by norm_num)]; exact hhi

end E8PConstants.VevWindow
