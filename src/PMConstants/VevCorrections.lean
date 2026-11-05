import PMConstants.VevAccounting
import PMConstants.PersistenceClosures
import PMConstants.RequirementRows

/-!
# What the Fermi window says about the VEV corrections

The VEV is `v = (χΔ² - 188) α⁻¹ m_e (1 + x)(1 - Y/3)`, `x = α/D_eff`, `D_eff = D + χ/(4π)`,
`Y = 1/(Δ² L_embed (σ+1))` (Paper I's margin). `ElectroweakBounds.vev_bounds` pins it to
`(246.2196378, 246.2196379)`, and the measured Fermi constant fixes `v_F ∈ (246.21957, 246.21971)`
(`VevAccounting.fermi_window`), a relative width of about `2.8·10⁻⁷`. Alternatives below are
written as the formula times the ratio of correction factors.

**The noise term is needed, and its divisor is `3` or `4`.**
* `noise_needed`: dropping `δ_noise` puts `v` above `246.21987`, outside the window.
* `divisor_window`: with divisor `k` (natural), `v` lies in the window exactly for `k = 3` or
  `k = 4`. The data cannot separate `σ - χ = 3` from `D = 4`.

**The topological term has exactly the stated form.**
* `exp_excluded`: `exp x` in place of `1 + x` puts `v` above `246.22001`.
* `geometric_excluded`: `1/(1 - x)` (the sum `Σ xᵏ`) puts `v` above `246.22038`.
* `bare_dimension_excluded`: `α/D` without the boundary term puts `v` above `246.2366`.
* `qed_like_excluded`: `3α/(4π)` puts `v` below `246.2167`.

**The boundary term.**
* `dimension_window`: the window pins the effective dimension to `(4.1584, 4.1599)`.
* `boundary_unique`: among `4 + a/(bπ)` with `b ≤ 200`, only `a/b = 1/2`, i.e. `χ/(4π)`, fits.

**Persistence readings (premises, named).**
* *One repair gives the linear form.* `1/(1 - x)` is repairs of repairs, `exp x` continuous
  compounding; the anchor's maintenance is one repair (`PersistenceClosures.one_repair`), which is
  exactly first order. The data reject both iterated forms.
* *The noise lands on the axes orthogonal to the reference.* The reference sits on the time axis
  (`RequirementRows.axis_symmetry_kept`) and is the maintained axis; the temporal noise is shared by
  the other `D - 1 = 3` axes, which are also the colour axes `σ - χ`. This picks `3` over `4`,
  which the data allow equally.
-/

noncomputable section
namespace PMConstants.VevCorrections
open PMConstants ElectroweakE8 CertifiedConstants ElectroweakBounds

def V : ℝ := vev α electronGeV
def Y : ℝ := bareYukawa
def x : ℝ := α / effectiveDimension

lemma V_bounds : (246.2196378 : ℝ) < V ∧ V < 246.2196379 := vev_bounds

lemma Y_val : Y = 1 / (31 * 6 * 43 ^ 2) := by
  unfold Y bareYukawa
  rw [PMSubstrate.E8Values.embeddingLoad_eq, PMSubstrate.E8Values.D_eq,
    PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.Delta_eq]
  norm_num

lemma x_bounds : (0.0017545277 : ℝ) < x ∧ x < 0.0017545279 := by
  have ha := alpha_bounds
  have hd := JointConstants.inverse_dimension_bounds
  have : x = α * (1 / effectiveDimension) := by unfold x; ring
  rw [this]; constructor <;> nlinarith [ha.1, ha.2, hd.1, hd.2]

/-- The formula with noise divisor `k`. -/
def withDivisor (k : ℝ) : ℝ := V * (1 - Y / k) / (1 - Y / 3)

theorem noise_needed : 246.21987 < V / (1 - Y / 3) := by
  have hv := V_bounds
  rw [lt_div_iff₀ (by norm_num [Y_val])]
  norm_num [Y_val]; nlinarith [hv.1]

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
    have hr2 : 1 / (k : ℝ) < 0.4282 := by
      by_contra hc; push Not at hc
      have : V * (1 - Y / k) ≤ V * (1 - Y * 0.4282) := by
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

theorem exp_excluded : 246.22001 < V * Real.exp x / (1 + x) := by
  have hv := V_bounds
  have hx := x_bounds
  have he : 1 + x + x ^ 2 / 2 ≤ Real.exp x := Real.quadratic_le_exp_of_nonneg (by linarith)
  rw [lt_div_iff₀ (by linarith)]
  have : V * (1 + x + x ^ 2 / 2) ≤ V * Real.exp x := mul_le_mul_of_nonneg_left he (by linarith)
  nlinarith

theorem geometric_excluded : 246.22038 < V / ((1 - x) * (1 + x)) := by
  have hv := V_bounds
  have hx := x_bounds
  rw [lt_div_iff₀ (by nlinarith)]
  nlinarith

theorem bare_dimension_excluded : 246.2366 < V * (1 + α / 4) / (1 + x) := by
  have hv := V_bounds
  have hx := x_bounds
  have ha := alpha_bounds
  rw [lt_div_iff₀ (by linarith)]
  nlinarith

theorem qed_like_excluded : V * (1 + 3 * α / (4 * Real.pi)) / (1 + x) < 246.2167 := by
  have hv := V_bounds
  have hx := x_bounds
  have ha := alpha_bounds
  have hp := pi_bounds
  have hq : 3 * α / (4 * Real.pi) < 0.0017422 := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  rw [div_lt_iff₀ (by linarith)]
  have h1 : V * (3 * α / (4 * Real.pi)) < V * 0.0017422 := mul_lt_mul_of_pos_left hq (by linarith)
  nlinarith

/-! ## The boundary term is exactly `χ/(4π)` -/

/-- The formula with effective dimension `Dp` in place of `D_eff`. -/
def withDimension (Dp : ℝ) : ℝ := V * (1 + α / Dp) / (1 + x)

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

end PMConstants.VevCorrections
