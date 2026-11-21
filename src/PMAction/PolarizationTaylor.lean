import PMAction.PolarizationIngredients

/-!
# Step (ii) of the subtracted lattice polarization, first part: per-root expansions in `q`

The route for step (ii) (`PMAction/TODO.md`): with the Ward identity
(`FiniteVertex.ward`), `S(k + q) = S(k) + ΔS` exactly, and `PolarizationAverage.inv_expand`
expands `1/S(k + q)` in `ΔS` with no Taylor step. All remaining `q`-dependence then sits in
trigonometric functions of `x = a r·q/2`, per root, times functions of `A = a r·k`. This module
gives their second-order expansions in `x` with explicit cubic remainders, valid for `|x| ≤ 1`
(on the shell `2|q| ≤ lo` with `a·hi ≤ 1`).

* `sinc_expand`: `|sinc x − (1 − x²/6)| ≤ |x|³/100`.
* `sin_shift_expand`: `|sin(A + x) − (sin A + x cos A − x²/2 · sin A)| ≤ (7/32)|x|³`.
* `leg_root_expand`: the leg's factor, `|sinc x · sin(A + x) − (sin A + x cos A − (2/3)x² sin A)|
  ≤ |x|³/2`.
* `contact_root_expand`: the contact's factor, `|cos A · sinc² x − cos A (1 − x²/3)| ≤ |x|³/16`.
* `dS_root_expand`: the propagator shift's factor (`FiniteVertex.contracted`),
  `|sin(A + x) sin x − (x sin A + x² cos A)| ≤ (3/2)|x|³`.

The next part collects these into the lattice integrand's `q²` coefficient (root sums of
trigonometric functions of `A`) and compares it with the continuum's `coefC`.
-/

noncomputable section
namespace PMAction.PolarizationTaylor
open Real

lemma cube_le {x : ℝ} (hx : |x| ≤ 1) : |x| ^ 4 ≤ |x| ^ 3 :=
  pow_le_pow_of_le_one (abs_nonneg x) hx (by norm_num)

/-- **`sinc` to second order.** -/
theorem sinc_expand {x : ℝ} (hx : |x| ≤ 1) : |sinc x - (1 - x ^ 2 / 6)| ≤ |x| ^ 3 / 100 := by
  by_cases h0 : x = 0
  · subst h0; simp [Real.sinc_zero]
  have e : sinc x - (1 - x ^ 2 / 6) = (sin x - (x - x ^ 3 / 6)) / x := by
    rw [Real.sinc_of_ne_zero h0]; field_simp
    try ring
  have hb := Real.sin_bound hx
  have h5 : |x| ^ 5 ≤ |x| ^ 4 := pow_le_pow_of_le_one (abs_nonneg x) hx (by norm_num)
  rw [e, abs_div, div_le_iff₀ (abs_pos.2 h0)]
  calc |sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 5 / 100 := hb
    _ ≤ |x| ^ 4 / 100 := by linarith
    _ = |x| ^ 3 / 100 * |x| := by ring

/-- **`sin(A + x)` to second order in `x`.** -/
theorem sin_shift_expand (A : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    |sin (A + x) - (sin A + x * cos A - x ^ 2 / 2 * sin A)| ≤ 7 / 32 * |x| ^ 3 := by
  have e : sin (A + x) - (sin A + x * cos A - x ^ 2 / 2 * sin A) =
      sin A * (cos x - (1 - x ^ 2 / 2)) + cos A * (sin x - x) := by rw [sin_add]; ring
  have hc : |cos x - (1 - x ^ 2 / 2)| ≤ |x| ^ 4 * (5 / 96) := Real.cos_bound hx
  have hs : |sin x - x| ≤ |x| ^ 3 / 6 := by rw [abs_sub_comm]; exact abs_sub_sin_le x
  have h4 := cube_le hx
  have t1 : |sin A * (cos x - (1 - x ^ 2 / 2))| ≤ |x| ^ 4 * (5 / 96) := by
    rw [abs_mul]
    calc |sin A| * |cos x - (1 - x ^ 2 / 2)| ≤ 1 * (|x| ^ 4 * (5 / 96)) :=
          mul_le_mul (abs_sin_le_one A) hc (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have t2 : |cos A * (sin x - x)| ≤ |x| ^ 3 / 6 := by
    rw [abs_mul]
    calc |cos A| * |sin x - x| ≤ 1 * (|x| ^ 3 / 6) :=
          mul_le_mul (abs_cos_le_one A) hs (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  rw [e]
  calc _ ≤ |sin A * (cos x - (1 - x ^ 2 / 2))| + |cos A * (sin x - x)| := abs_add_le _ _
    _ ≤ |x| ^ 4 * (5 / 96) + |x| ^ 3 / 6 := add_le_add t1 t2
    _ ≤ 7 / 32 * |x| ^ 3 := by linarith

/-- **The leg's per-root factor to second order.** -/
theorem leg_root_expand (A : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    |sinc x * sin (A + x) - (sin A + x * cos A - 2 / 3 * x ^ 2 * sin A)| ≤ |x| ^ 3 / 2 := by
  have key : sinc x * sin (A + x) - (sin A + x * cos A - 2 / 3 * x ^ 2 * sin A) =
      -(x ^ 3 / 6 * cos A) + x ^ 4 / 12 * sin A + (sinc x - (1 - x ^ 2 / 6)) * sin (A + x) +
        (1 - x ^ 2 / 6) * (sin (A + x) - (sin A + x * cos A - x ^ 2 / 2 * sin A)) := by ring
  have h4 := cube_le hx
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have b1 : |-(x ^ 3 / 6 * cos A)| ≤ |x| ^ 3 / 6 := by
    rw [abs_neg, abs_mul, abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    exact mul_le_of_le_one_right (by positivity) (abs_cos_le_one A)
  have b2 : |x ^ 4 / 12 * sin A| ≤ |x| ^ 3 / 12 := by
    rw [abs_mul, abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
    calc |x| ^ 4 / 12 * |sin A| ≤ |x| ^ 4 / 12 * 1 :=
          mul_le_mul_of_nonneg_left (abs_sin_le_one A) (by positivity)
      _ ≤ |x| ^ 3 / 12 := by linarith
  have b3 : |(sinc x - (1 - x ^ 2 / 6)) * sin (A + x)| ≤ |x| ^ 3 / 100 := by
    rw [abs_mul]
    calc _ ≤ |x| ^ 3 / 100 * 1 :=
          mul_le_mul (sinc_expand hx) (abs_sin_le_one _) (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  have b4 : |(1 - x ^ 2 / 6) * (sin (A + x) - (sin A + x * cos A - x ^ 2 / 2 * sin A))| ≤
      7 / 32 * |x| ^ 3 := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    calc _ ≤ 1 * (7 / 32 * |x| ^ 3) :=
          mul_le_mul (by linarith [sq_nonneg x]) (sin_shift_expand A hx) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  rw [key]
  have := abs_add_le (-(x ^ 3 / 6 * cos A) + x ^ 4 / 12 * sin A +
      (sinc x - (1 - x ^ 2 / 6)) * sin (A + x))
    ((1 - x ^ 2 / 6) * (sin (A + x) - (sin A + x * cos A - x ^ 2 / 2 * sin A)))
  have := abs_add_le (-(x ^ 3 / 6 * cos A) + x ^ 4 / 12 * sin A)
    ((sinc x - (1 - x ^ 2 / 6)) * sin (A + x))
  have := abs_add_le (-(x ^ 3 / 6 * cos A)) (x ^ 4 / 12 * sin A)
  have hx3 : 0 ≤ |x| ^ 3 := by positivity
  linarith

/-- **The contact's per-root factor to second order.** -/
theorem contact_root_expand (A : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    |cos A * sinc x ^ 2 - cos A * (1 - x ^ 2 / 3)| ≤ |x| ^ 3 / 16 := by
  set e := sinc x - (1 - x ^ 2 / 6) with he
  have hb : |e| ≤ |x| ^ 3 / 100 := sinc_expand hx
  have key : cos A * sinc x ^ 2 - cos A * (1 - x ^ 2 / 3) =
      cos A * (x ^ 4 / 36 + 2 * e * (1 - x ^ 2 / 6) + e ^ 2) := by rw [he]; ring
  have h4 := cube_le hx
  have hx3 : |x| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have hx4 : x ^ 4 = |x| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have inner : |x ^ 4 / 36 + 2 * e * (1 - x ^ 2 / 6) + e ^ 2| ≤ |x| ^ 3 / 16 := by
    have c1 : |x ^ 4 / 36| ≤ |x| ^ 3 / 36 := by
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4),
        abs_of_pos (by norm_num : (0 : ℝ) < 36), hx4]
      linarith
    have c2 : |2 * e * (1 - x ^ 2 / 6)| ≤ 2 * (|x| ^ 3 / 100) := by
      rw [abs_mul, abs_mul, abs_two, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - x ^ 2 / 6)]
      nlinarith [abs_nonneg e, hb, hx2]
    have c3 : |e ^ 2| ≤ |x| ^ 3 / 10000 := by
      rw [abs_pow]
      have h1 : |e| ^ 2 ≤ (|x| ^ 3 / 100) ^ 2 := pow_le_pow_left₀ (abs_nonneg e) hb 2
      have h2 : (|x| ^ 3) ^ 2 ≤ |x| ^ 3 := by nlinarith [hx3, pow_nonneg (abs_nonneg x) 3]
      have h3 : (|x| ^ 3 / 100) ^ 2 = (|x| ^ 3) ^ 2 / 10000 := by ring
      linarith
    have := abs_add_le (x ^ 4 / 36 + 2 * e * (1 - x ^ 2 / 6)) (e ^ 2)
    have := abs_add_le (x ^ 4 / 36) (2 * e * (1 - x ^ 2 / 6))
    have : 0 ≤ |x| ^ 3 := by positivity
    linarith
  rw [key, abs_mul]
  calc _ ≤ 1 * (|x| ^ 3 / 16) := mul_le_mul (abs_cos_le_one A) inner (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **The propagator shift's per-root factor to second order.** -/
theorem dS_root_expand (A : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    |sin (A + x) * sin x - (x * sin A + x ^ 2 * cos A)| ≤ 3 / 2 * |x| ^ 3 := by
  set Q := sin A + x * cos A - x ^ 2 / 2 * sin A with hQ
  set e3 := sin (A + x) - Q with he3
  set e2 := sin x - x with he2
  have key : sin (A + x) * sin x - (x * sin A + x ^ 2 * cos A) =
      -(x ^ 3 / 2 * sin A) + Q * e2 + e3 * x + e3 * e2 := by rw [he3, he2, hQ]; ring
  have b3 : |e3| ≤ 7 / 32 * |x| ^ 3 := sin_shift_expand A hx
  have b2 : |e2| ≤ |x| ^ 3 / 6 := by rw [he2, abs_sub_comm]; exact abs_sub_sin_le x
  have h4 := cube_le hx
  have hx3 : |x| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  have hQb : |Q| ≤ 5 / 2 := by
    have u1 := abs_le.1 (abs_sin_le_one A)
    have u2 : |x * cos A| ≤ 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg x, abs_nonneg (cos A), abs_cos_le_one A]
    have u3 : |x ^ 2 / 2 * sin A| ≤ 1 / 2 := by
      have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2 / 2)]
      nlinarith [abs_nonneg (sin A), abs_sin_le_one A]
    have v2 := abs_le.1 u2
    have v3 := abs_le.1 u3
    rw [hQ]
    exact abs_le.2 ⟨by linarith [u1.1, v2.1, v3.2], by linarith [u1.2, v2.2, v3.1]⟩
  have t1 : |-(x ^ 3 / 2 * sin A)| ≤ |x| ^ 3 / 2 := by
    rw [abs_neg, abs_mul, abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_of_le_one_right (by positivity) (abs_sin_le_one A)
  have t2 : |Q * e2| ≤ 5 / 2 * (|x| ^ 3 / 6) := by
    rw [abs_mul]; exact mul_le_mul hQb b2 (abs_nonneg _) (by norm_num)
  have t3 : |e3 * x| ≤ 7 / 32 * |x| ^ 3 := by
    rw [abs_mul]
    calc |e3| * |x| ≤ 7 / 32 * |x| ^ 3 * 1 := mul_le_mul b3 hx (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  have t4 : |e3 * e2| ≤ 7 / 32 * |x| ^ 3 * (1 / 6) := by
    rw [abs_mul]
    exact mul_le_mul b3 (by linarith) (abs_nonneg _) (by positivity)
  rw [key]
  have := abs_add_le (-(x ^ 3 / 2 * sin A) + Q * e2 + e3 * x) (e3 * e2)
  have := abs_add_le (-(x ^ 3 / 2 * sin A) + Q * e2) (e3 * x)
  have := abs_add_le (-(x ^ 3 / 2 * sin A)) (Q * e2)
  have : 0 ≤ |x| ^ 3 := by positivity
  linarith

end PMAction.PolarizationTaylor
