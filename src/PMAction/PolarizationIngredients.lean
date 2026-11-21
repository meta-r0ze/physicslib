import PMAction.PolarizationContact

/-!
# Step (i) of the subtracted lattice polarization: pointwise `O(a²)` ingredient bounds

`PMAction/TODO.md` ("Subtracted lattice polarization"): bound the lattice polarization
against the continuum after subtracting `q = 0`, resolving the `q²` coefficient
(`tools/lattice_polarization_check.py`: the difference is `C a² (hi² − lo²)`, `C ≈ 1.38`). This
module is step (i): each lattice ingredient against its continuum form, per root, so the later
steps can sum them. The propagator's bound is `LeadingLog.symbol_gap`.

* `sinc_sub_one`: `|sinc x − 1| ≤ x²/6`.
* `sinc_sin_gap`: `|sinc y · sin B − B| ≤ |B|³/6 + y²/6 · |B|`.
* `leg_gap`: the sinc-weighted midpoint leg of `PolarizationContact` against
  `Σ_r (r·v)(r·w)/6`, `w = k + q/2` (which is `2 w·v`, `LeadingLog.cross_moment`):
  `≤ Σ_r |r·v| (a²|r·w|³/6 + (a r·q/2)²/6 · |r·w|) / 6`.
* `cos_sinc_sq_gap`: `|cos A · sinc² y − 1| ≤ A²/2 + y²/6 · (2 + y²/6)`.
* `contact_gap`: the contact against `Σ_r (r·u)(r·v)/6` (which is `2 u·v`):
  `≤ Σ_r |r·u||r·v| (A_r²/2 + y_r²/6 · (2 + y_r²/6)) / 6`, `A_r = a r·k`, `y_r = a r·q/2`.

Every bound is `a²` times a polynomial in `|k|`, `|q|` (`|r·x| ≤ √2 |x|`).
-/

noncomputable section
namespace PMAction.PolarizationIngredients
open Real D4Gauge LeadingLog PolarizationContact

/-- **`|sinc x − 1| ≤ x²/6`.** -/
theorem sinc_sub_one (x : ℝ) : |sinc x - 1| ≤ x ^ 2 / 6 := by
  by_cases hx : x = 0
  · simp [hx, Real.sinc_zero]
  · rw [Real.sinc_of_ne_zero hx, div_sub_one hx, abs_div, div_le_iff₀ (abs_pos.2 hx)]
    calc |sin x - x| = |x - sin x| := abs_sub_comm _ _
      _ ≤ |x| ^ 3 / 6 := abs_sub_sin_le x
      _ = x ^ 2 / 6 * |x| := by rw [show |x| ^ 3 = |x| ^ 2 * |x| by ring, sq_abs]; ring

/-- **The weighted sine against its argument.** -/
theorem sinc_sin_gap (y B : ℝ) : |sinc y * sin B - B| ≤ |B| ^ 3 / 6 + y ^ 2 / 6 * |B| := by
  have e : sinc y * sin B - B = (sin B - B) + (sinc y - 1) * sin B := by ring
  have h1 : |sin B - B| ≤ |B| ^ 3 / 6 := by rw [abs_sub_comm]; exact abs_sub_sin_le B
  have h2 : |(sinc y - 1) * sin B| ≤ y ^ 2 / 6 * |B| := by
    rw [abs_mul]
    exact mul_le_mul (sinc_sub_one y) Real.abs_sin_le_abs (abs_nonneg _) (by positivity)
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- One root's leg gap. -/
theorem leg_root_gap {a : ℝ} (ha : 0 < a) (V W y : ℝ) :
    |V * sinc y * sin (a * W) / (6 * a) - V * W / 6| ≤
      |V| * (a ^ 2 * |W| ^ 3 / 6 + y ^ 2 / 6 * |W|) / 6 := by
  have ha0 : a ≠ 0 := ha.ne'
  have e : V * sinc y * sin (a * W) / (6 * a) - V * W / 6 =
      V * (sinc y * sin (a * W) - a * W) / (6 * a) := by
    field_simp
    try ring
  have h := sinc_sin_gap y (a * W)
  rw [e, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 6 * a),
    div_le_iff₀ (by positivity)]
  calc |V| * |sinc y * sin (a * W) - a * W|
      ≤ |V| * (|a * W| ^ 3 / 6 + y ^ 2 / 6 * |a * W|) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = |V| * (a ^ 2 * |W| ^ 3 / 6 + y ^ 2 / 6 * |W|) / 6 * (6 * a) := by
        rw [abs_mul, abs_of_pos ha]; ring

/-- **The sinc-weighted midpoint leg against its continuum root sum.** -/
theorem leg_gap {a : ℝ} (ha : 0 < a) (k q v : Fin 4 → ℝ) :
    |leg a k q v 1 - (∑ r ∈ roots, rk r v * (rk r k + rk r q / 2)) / 6| ≤
      (∑ r ∈ roots, |rk r v| * (a ^ 2 * |rk r k + rk r q / 2| ^ 3 / 6 +
        (a * rk r q / 2) ^ 2 / 6 * |rk r k + rk r q / 2|)) / 6 := by
  have hl : leg a k q v 1 = ∑ r ∈ roots,
      rk r v * sinc (a * rk r q / 2) * sin (a * (rk r k + rk r q / 2)) / (6 * a) := by
    rw [leg, Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 3; ring
  rw [hl, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  exact leg_root_gap ha _ _ _

/-- **`cos A · sinc² y` against `1`.** -/
theorem cos_sinc_sq_gap (A y : ℝ) :
    |cos A * sinc y ^ 2 - 1| ≤ A ^ 2 / 2 + y ^ 2 / 6 * (2 + y ^ 2 / 6) := by
  have hs := sinc_sub_one y
  have hc1 : |cos A - 1| ≤ A ^ 2 / 2 := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [cos_le_one A])]
    linarith [one_sub_sq_div_two_le_cos (x := A)]
  have hplus : |sinc y + 1| ≤ 2 + y ^ 2 / 6 := by
    calc |sinc y + 1| = |(sinc y - 1) + 2| := by congr 1; ring
      _ ≤ |sinc y - 1| + |(2 : ℝ)| := abs_add_le _ _
      _ ≤ y ^ 2 / 6 + 2 := by rw [abs_two]; linarith
      _ = 2 + y ^ 2 / 6 := by ring
  have hsq : |sinc y ^ 2 - 1| ≤ y ^ 2 / 6 * (2 + y ^ 2 / 6) := by
    rw [show sinc y ^ 2 - 1 = (sinc y - 1) * (sinc y + 1) by ring, abs_mul]
    exact mul_le_mul hs hplus (abs_nonneg _) (by positivity)
  have e : cos A * sinc y ^ 2 - 1 = (cos A - 1) + cos A * (sinc y ^ 2 - 1) := by ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add hc1 ?_)
  rw [abs_mul]
  calc |cos A| * |sinc y ^ 2 - 1| ≤ 1 * |sinc y ^ 2 - 1| :=
        mul_le_mul_of_nonneg_right (abs_cos_le_one A) (abs_nonneg _)
    _ ≤ y ^ 2 / 6 * (2 + y ^ 2 / 6) := by rw [one_mul]; exact hsq

/-- **The contact against its continuum root sum.** -/
theorem contact_gap (a : ℝ) (k q u v : Fin 4 → ℝ) :
    |contact a k q u v - (∑ r ∈ roots, rk r u * rk r v) / 6| ≤
      (∑ r ∈ roots, |rk r u| * |rk r v| * ((a * rk r k) ^ 2 / 2 +
        (a * rk r q / 2) ^ 2 / 6 * (2 + (a * rk r q / 2) ^ 2 / 6))) / 6 := by
  rw [contact, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  have e : cos (a * rk r k) * (rk r u * sinc (a * rk r q / 2)) * (rk r v * sinc (a * rk r q / 2)) -
      rk r u * rk r v = rk r u * rk r v * (cos (a * rk r k) * sinc (a * rk r q / 2) ^ 2 - 1) := by
    ring
  rw [e, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (cos_sinc_sq_gap _ _) (by positivity)

end PMAction.PolarizationIngredients
