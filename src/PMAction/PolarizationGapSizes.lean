import PMAction.PolarizationMagnitudes

/-!
# Sizes of the gaps between the lattice orders and the continuum's

`PolarizationOrders` bounds each order against its continuum root sum, and `conv_*` turns the root
sums into the continuum's values. With `PolarizationMagnitudes`' `n` and `24` roots, for `a > 0`:

* `l0_close`: `|l₀ − 2u·k| ≤ (2/3) a² n(u) n(k)³`;
* `l1_close`: `|l₁ − u·q| ≤ a² n(u) n(k)² n(q)`;
* `s1_close`: `|s₁ − 2q·k| ≤ (2/3) a² n(k)³ n(q)`;
* `s2_close`: `|s₂ − q·q| ≤ a² n(k)² n(q)²`.

(`l₂` and `c₂`, whose continuum values are `0`, are `PolarizationMagnitudes.l2_le`, `c2_le`.)
-/

noncomputable section
namespace PMAction.PolarizationGapSizes
open Real D4Gauge LeadingLog PolarizationOrders PolarizationMagnitudes

lemma sq_le_of_abs {x X : ℝ} (h : |x| ≤ X) : x ^ 2 ≤ X ^ 2 := by
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2

theorem l0_close {a : ℝ} (ha : 0 < a) (k u : Fin 4 → ℝ) :
    |l0 a k u - 2 * dot u k| ≤ 2 / 3 * a ^ 2 * n1 u * n1 k ^ 3 := by
  have g := l0_gap ha k u
  rw [conv_l0 ha] at g
  refine g.trans ?_
  rw [div_le_iff₀ (by positivity)]
  refine (le_abs_self _).trans ((root_sum_bound (c := n1 u * ((a * n1 k) ^ 3 / 6))
    fun r _ => ?_).trans (le_of_eq (by ring)))
  rw [abs_of_nonneg (by positivity)]
  exact mul_le_mul (rk_le r u) (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) (hA_le ha r k) 3) (by norm_num)) (by positivity) (n1_nonneg u)

theorem l1_close {a : ℝ} (ha : 0 < a) (k q u : Fin 4 → ℝ) :
    |l1 a k q u - dot u q| ≤ a ^ 2 * n1 u * n1 k ^ 2 * n1 q := by
  have g := l1_gap ha k q u
  rw [conv_l1 ha] at g
  refine g.trans ?_
  rw [div_le_iff₀ (by positivity)]
  refine (le_abs_self _).trans ((root_sum_bound
    (c := n1 u * ((a * n1 q / 2) * ((a * n1 k) ^ 2 / 2))) fun r _ => ?_).trans (le_of_eq (by ring)))
  rw [abs_of_nonneg (by positivity)]
  refine mul_le_mul (rk_le r u) (mul_le_mul (hx_le ha r q) (div_le_div_of_nonneg_right
    (sq_le_of_abs (hA_le ha r k)) (by norm_num)) (by positivity) (by positivity)) (by positivity)
    (n1_nonneg u)

theorem s1_close {a : ℝ} (ha : 0 < a) (k q : Fin 4 → ℝ) :
    |s1 a k q - 2 * dot q k| ≤ 2 / 3 * a ^ 2 * n1 k ^ 3 * n1 q := by
  have g := s1_gap ha k q
  rw [conv_s1 ha] at g
  refine g.trans ?_
  rw [div_le_iff₀ (by positivity)]
  refine (le_abs_self _).trans ((root_sum_bound
    (c := 2 * ((a * n1 q / 2) * ((a * n1 k) ^ 3 / 6))) fun r _ => ?_).trans (le_of_eq (by ring)))
  rw [abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (hx_le ha r q) (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) (hA_le ha r k) 3) (by norm_num)) (by positivity)
    (by positivity)) (by norm_num)

theorem s2_close {a : ℝ} (ha : 0 < a) (k q : Fin 4 → ℝ) :
    |s2 a k q - dot q q| ≤ a ^ 2 * n1 k ^ 2 * n1 q ^ 2 := by
  have g := s2_gap ha k q
  rw [conv_s2 ha] at g
  refine g.trans ?_
  rw [div_le_iff₀ (by positivity)]
  refine (le_abs_self _).trans ((root_sum_bound
    (c := 2 * ((a * n1 q / 2) ^ 2 * ((a * n1 k) ^ 2 / 2))) fun r _ => ?_).trans (le_of_eq (by ring)))
  rw [abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (sq_le_of_abs (hx_le ha r q))
    (div_le_div_of_nonneg_right (sq_le_of_abs (hA_le ha r k)) (by norm_num)) (by positivity)
    (by positivity)) (by norm_num)

end PMAction.PolarizationGapSizes
