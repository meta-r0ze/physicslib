import PMAction.PolarizationCubic

/-!
# Step (ii.e) of the subtracted lattice polarization: the second order against the continuum's

`PolarizationAssembly.Q` is the second-order part of the integrand in terms of the orders. With the
continuum's orders (`PolarizationOrders.conv_*`: `P₀ = 2k·u`, `P₁ = q·u`, `P₂ = 0`, `D₁ = 2k·q`,
`D₂ = q·q`, `C₂ = 0`, `S_c = |k|²`) it is the continuum's `q²` coefficient
(`ShellMoments.coefC`, by direct expansion). This module bounds the lattice `Q` against the
continuum `Q` by the differences of the orders.

* `frac_diff`: `|N/Sⁿ − N_c/S_cⁿ| ≤ |N − N_c|/σⁿ + |N_c| · |S − S_c| n Mⁿ⁻¹/σ²ⁿ` for
  `σ ≤ S, S_c` and `|S|, |S_c| ≤ M` (`abs_pow_sub_pow_le`).
* `Q_diff`: `|Q_lat − Q_cont|` is at most the sum of `frac_diff` over its five terms.

The numerator differences come from `PolarizationOrders` (each `O(a²)`) and `symbol_gap`
(`|S − |k|²| ≤ a²|k|⁴/12`).
-/

noncomputable section
namespace PMAction.PolarizationQDiff
open PolarizationAssembly

/-- The bound of `frac_diff`. -/
def fb (σ M dS : ℝ) (n : ℕ) (X Y : ℝ) : ℝ := X / σ ^ n + Y * (dS * n * M ^ (n - 1)) / (σ ^ n * σ ^ n)

/-- **A fraction against its continuum counterpart.** -/
theorem frac_diff {N Nc S Sc σ M : ℝ} (n : ℕ) (hσ : 0 < σ) (hS : σ ≤ S) (hSc : σ ≤ Sc)
    (hM : |S| ≤ M) (hMc : |Sc| ≤ M) :
    |N / S ^ n - Nc / Sc ^ n| ≤ fb σ M |S - Sc| n |N - Nc| |Nc| := by
  have hS0 : 0 < S := hσ.trans_le hS
  have hSc0 : 0 < Sc := hσ.trans_le hSc
  have pS : σ ^ n ≤ S ^ n := pow_le_pow_left₀ hσ.le hS n
  have pSc : σ ^ n ≤ Sc ^ n := pow_le_pow_left₀ hσ.le hSc n
  have e : N / S ^ n - Nc / Sc ^ n = (N - Nc) / S ^ n + Nc * (Sc ^ n - S ^ n) / (S ^ n * Sc ^ n) := by
    field_simp
    try ring
  have hp : |Sc ^ n - S ^ n| ≤ |S - Sc| * n * M ^ (n - 1) := by
    refine (abs_pow_sub_pow_le ..).trans ?_
    rw [abs_sub_comm Sc S]
    gcongr
    exact max_le hMc hM
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  rw [e]
  unfold fb
  have pS0 : 0 < S ^ n := pow_pos hS0 n
  have pSc0 : 0 < Sc ^ n := pow_pos hSc0 n
  have pσ : 0 < σ ^ n := pow_pos hσ n
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos pS0]
    exact div_le_div₀ (abs_nonneg _) le_rfl pσ pS
  · rw [abs_div, abs_mul, abs_of_pos (mul_pos pS0 pSc0)]
    refine div_le_div₀ (mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (abs_nonneg _)
      (Nat.cast_nonneg _)) (pow_nonneg hM0 _))) ?_ (mul_pos pσ pσ)
      (mul_le_mul pS pSc pσ.le pS0.le)
    exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)

/-- **The lattice second order against the continuum's.** The continuum values have `P₂ = V₂ = 0`
and `C₂ = 0`. -/
theorem Q_diff {S Sc σ M p0 p1 p2 v0 v1 v2 d1 d2 c2 P0 P1 V0 V1 D1 D2 : ℝ}
    (hσ : 0 < σ) (hS : σ ≤ S) (hSc : σ ≤ Sc) (hM : |S| ≤ M) (hMc : |Sc| ≤ M) :
    |Q S p0 p1 p2 v0 v1 v2 d1 d2 c2 - Q Sc P0 P1 0 V0 V1 0 D1 D2 0| ≤
      fb σ M |S - Sc| 2 |(p1 * v1 + p0 * v2 + p2 * v0) - (P1 * V1 + P0 * 0 + 0 * V0)|
          |P1 * V1 + P0 * 0 + 0 * V0| +
        fb σ M |S - Sc| 3 |(p0 * v1 + p1 * v0) * d1 - (P0 * V1 + P1 * V0) * D1| |(P0 * V1 + P1 * V0) * D1| +
        fb σ M |S - Sc| 3 |p0 * v0 * d2 - P0 * V0 * D2| |P0 * V0 * D2| +
        fb σ M |S - Sc| 4 |p0 * v0 * d1 ^ 2 - P0 * V0 * D1 ^ 2| |P0 * V0 * D1 ^ 2| +
        fb σ M |S - Sc| 1 |c2 - 0| |(0 : ℝ)| := by
  have e : Q S p0 p1 p2 v0 v1 v2 d1 d2 c2 - Q Sc P0 P1 0 V0 V1 0 D1 D2 0 =
      ((p1 * v1 + p0 * v2 + p2 * v0) / S ^ 2 - (P1 * V1 + P0 * 0 + 0 * V0) / Sc ^ 2) -
        ((p0 * v1 + p1 * v0) * d1 / S ^ 3 - (P0 * V1 + P1 * V0) * D1 / Sc ^ 3) -
        (p0 * v0 * d2 / S ^ 3 - P0 * V0 * D2 / Sc ^ 3) +
        (p0 * v0 * d1 ^ 2 / S ^ 4 - P0 * V0 * D1 ^ 2 / Sc ^ 4) -
        (c2 / S ^ 1 - 0 / Sc ^ 1) := by
    unfold Q; simp only [pow_one]; ring
  rw [e]
  have t1 := frac_diff (N := p1 * v1 + p0 * v2 + p2 * v0) (Nc := P1 * V1 + P0 * 0 + 0 * V0) 2 hσ hS hSc hM hMc
  have t2 := frac_diff (N := (p0 * v1 + p1 * v0) * d1) (Nc := (P0 * V1 + P1 * V0) * D1) 3 hσ hS hSc hM hMc
  have t3 := frac_diff (N := p0 * v0 * d2) (Nc := P0 * V0 * D2) 3 hσ hS hSc hM hMc
  have t4 := frac_diff (N := p0 * v0 * d1 ^ 2) (Nc := P0 * V0 * D1 ^ 2) 4 hσ hS hSc hM hMc
  have t5 := frac_diff (N := c2) (Nc := (0 : ℝ)) 1 hσ hS hSc hM hMc
  have := abs_le.1 t1; have := abs_le.1 t2; have := abs_le.1 t3; have := abs_le.1 t4
  have := abs_le.1 t5
  exact abs_le.2 ⟨by linarith, by linarith⟩

end PMAction.PolarizationQDiff
