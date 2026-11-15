import PMAction.PolarizationOrders

/-!
# Magnitudes of the orders of the lattice polarization's ingredients

For the assembly (`PolarizationAssembly`) each order of `PolarizationOrders` and each remainder of
`PolarizationSplit` needs a size. With `n w = Σᵢ |wᵢ|` (`rk_le`: `|r·w| ≤ n w` for every `D₄` root)
and the `24` roots (`root_sum_bound`), for `a > 0`:

| order | bound |
|---|---|
| `l0` | `4 n(u) n(k)` |
| `l1` | `2 n(u) n(q)` |
| `l2` | `(2/3) a² n(u) n(q)² n(k)` |
| leg remainder | `a² n(u) n(q)³ / 4` |
| `s1` | `4 n(q) n(k)` |
| `s2` | `2 n(q)²` |
| shift remainder | `(3/2) a n(q)³` |
| `c2` | `a² n(u) n(v) n(q)² / 3` |
| contact remainder | `a³ n(u) n(v) n(q)³ / 32` |
-/

noncomputable section
namespace PMAction.PolarizationMagnitudes
open Real D4Gauge LeadingLog PolarizationSplit PolarizationOrders PolarizationAverage

/-- The `ℓ¹` size of a momentum. -/
abbrev n1 (w : Fin 4 → ℝ) : ℝ := ∑ i, |w i|

lemma n1_nonneg (w : Fin 4 → ℝ) : 0 ≤ n1 w := Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **A root projection is at most the `ℓ¹` size.** -/
lemma rk_le (r : Fin 4 → Fin 3) (w : Fin 4 → ℝ) : |rk r w| ≤ n1 w := by
  unfold rk n1
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  calc |(vec r i : ℝ)| * |w i| ≤ 1 * |w i| :=
        mul_le_mul_of_nonneg_right (vec_abs r i) (abs_nonneg _)
    _ = |w i| := one_mul _

/-- **A root sum of terms bounded by `c` is at most `24 c`.** -/
lemma root_sum_bound {f : (Fin 4 → Fin 3) → ℝ} {c : ℝ} (h : ∀ r ∈ roots, |f r| ≤ c) :
    |∑ r ∈ roots, f r| ≤ 24 * c := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_card_nsmul _ _ _ h).trans ?_)
  rw [roots_card, nsmul_eq_mul]; norm_num

lemma hx_le {a : ℝ} (ha : 0 < a) (r : Fin 4 → Fin 3) (q : Fin 4 → ℝ) :
    |a * rk r q / 2| ≤ a * n1 q / 2 := by
  rw [abs_div, abs_mul, abs_of_pos ha, abs_two]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (rk_le r q) ha.le) (by norm_num)

lemma hA_le {a : ℝ} (ha : 0 < a) (r : Fin 4 → Fin 3) (k : Fin 4 → ℝ) :
    |a * rk r k| ≤ a * n1 k := by
  rw [abs_mul, abs_of_pos ha]; exact mul_le_mul_of_nonneg_left (rk_le r k) ha.le

/-- A quotient by `c > 0` from a numerator bound. -/
lemma div_bound {x c B : ℝ} (hc : 0 < c) (h : |x| ≤ B * c) : |x / c| ≤ B := by
  rw [abs_div, abs_of_pos hc, div_le_iff₀ hc]; exact h

theorem l0_le {a : ℝ} (ha : 0 < a) (k u : Fin 4 → ℝ) : |l0 a k u| ≤ 4 * n1 u * n1 k := by
  refine div_bound (by positivity) ((root_sum_bound (c := n1 u * (a * n1 k)) fun r _ => ?_).trans
    (le_of_eq (by ring)))
  rw [abs_mul]
  exact mul_le_mul (rk_le r u) (Real.abs_sin_le_abs.trans (hA_le ha r k)) (abs_nonneg _)
    (n1_nonneg u)

theorem l1_le {a : ℝ} (ha : 0 < a) (k q u : Fin 4 → ℝ) : |l1 a k q u| ≤ 2 * n1 u * n1 q := by
  refine div_bound (by positivity) ((root_sum_bound (c := n1 u * (a * n1 q / 2)) fun r _ => ?_).trans
    (le_of_eq (by ring)))
  rw [abs_mul, abs_mul]
  refine mul_le_mul (rk_le r u) ?_ (by positivity) (n1_nonneg u)
  calc |a * rk r q / 2| * |cos (a * rk r k)| ≤ (a * n1 q / 2) * 1 :=
        mul_le_mul (hx_le ha r q) (abs_cos_le_one _) (abs_nonneg _) (by positivity)
    _ = _ := mul_one _

theorem l2_le {a : ℝ} (ha : 0 < a) (k q u : Fin 4 → ℝ) :
    |l2 a k q u| ≤ 2 / 3 * a ^ 2 * n1 u * n1 q ^ 2 * n1 k := by
  have hq := n1_nonneg q; have hk := n1_nonneg k; have hu := n1_nonneg u
  refine div_bound (by positivity) ((root_sum_bound
    (c := n1 u * (2 / 3 * (a * n1 q / 2) ^ 2 * (a * n1 k))) fun r _ => ?_).trans
    (le_of_eq (by ring)))
  rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3), abs_pow]
  refine mul_le_mul (rk_le r u) ?_ (by positivity) hu
  refine mul_le_mul (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg _) (hx_le ha r q) 2) (by norm_num))
    (Real.abs_sin_le_abs.trans (hA_le ha r k)) (abs_nonneg _) (by positivity)

theorem legE_le {a : ℝ} (ha : 0 < a) (q u : Fin 4 → ℝ) :
    (∑ r ∈ roots, |rk r u| * (|a * rk r q / 2| ^ 3 / 2)) / (6 * a) ≤
      a ^ 2 * n1 u * n1 q ^ 3 / 4 := by
  have hq := n1_nonneg q; have hu := n1_nonneg u
  rw [div_le_iff₀ (by positivity)]
  refine (le_abs_self _).trans ((root_sum_bound (c := n1 u * ((a * n1 q / 2) ^ 3 / 2))
    fun r _ => ?_).trans (le_of_eq (by ring)))
  rw [abs_of_nonneg (by positivity)]
  exact mul_le_mul (rk_le r u) (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) (hx_le ha r q) 3) (by norm_num)) (by positivity) hu

theorem s1_le {a : ℝ} (ha : 0 < a) (k q : Fin 4 → ℝ) : |s1 a k q| ≤ 4 * n1 q * n1 k := by
  have hq := n1_nonneg q; have hk := n1_nonneg k
  refine div_bound (by positivity) ((root_sum_bound
    (c := 2 * ((a * n1 q / 2) * (a * n1 k))) fun r _ => ?_).trans (le_of_eq (by ring)))
  rw [abs_mul, abs_two, abs_mul]
  gcongr
  · exact hx_le ha r q
  · exact Real.abs_sin_le_abs.trans (hA_le ha r k)

theorem s2_le {a : ℝ} (ha : 0 < a) (k q : Fin 4 → ℝ) : |s2 a k q| ≤ 2 * n1 q ^ 2 := by
  have hq := n1_nonneg q
  refine div_bound (by positivity) ((root_sum_bound
    (c := 2 * ((a * n1 q / 2) ^ 2 * 1)) fun r _ => ?_).trans (le_of_eq (by ring)))
  rw [abs_mul, abs_two, abs_mul, abs_pow]
  gcongr
  · exact hx_le ha r q
  · exact abs_cos_le_one _

theorem dSE_le {a : ℝ} (ha : 0 < a) (q : Fin 4 → ℝ) :
    (∑ r ∈ roots, 3 * |a * rk r q / 2| ^ 3) / (6 * a ^ 2) ≤ 3 / 2 * a * n1 q ^ 3 := by
  have hq := n1_nonneg q
  rw [div_le_iff₀ (by positivity)]
  refine (le_abs_self _).trans ((root_sum_bound (c := 3 * (a * n1 q / 2) ^ 3)
    fun r _ => ?_).trans (le_of_eq (by ring)))
  rw [abs_of_nonneg (by positivity)]
  gcongr; exact hx_le ha r q

theorem c2_le {a : ℝ} (ha : 0 < a) (k q u v : Fin 4 → ℝ) :
    |c2 a k q u v| ≤ a ^ 2 * n1 u * n1 v * n1 q ^ 2 / 3 := by
  have hq := n1_nonneg q; have hu := n1_nonneg u; have hv := n1_nonneg v
  refine div_bound (by norm_num) ((root_sum_bound
    (c := n1 u * n1 v * ((a * n1 q / 2) ^ 2 / 3)) fun r _ => ?_).trans (le_of_eq (by ring)))
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_div, abs_pow,
    abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hc := abs_cos_le_one (a * rk r k)
  have h2 := pow_le_pow_left₀ (abs_nonneg _) (hx_le ha r q) 2
  calc |rk r u| * |rk r v| * (|cos (a * rk r k)| * (|a * rk r q / 2| ^ 2 / 3))
      ≤ n1 u * n1 v * (1 * ((a * n1 q / 2) ^ 2 / 3)) := by
        gcongr
        · exact rk_le r u
        · exact rk_le r v
    _ = _ := by ring

theorem cE_le {a : ℝ} (ha : 0 < a) (q u v : Fin 4 → ℝ) :
    (∑ r ∈ roots, |rk r u| * |rk r v| * (|a * rk r q / 2| ^ 3 / 16)) / 6 ≤
      a ^ 3 * n1 u * n1 v * n1 q ^ 3 / 32 := by
  have hq := n1_nonneg q; have hu := n1_nonneg u; have hv := n1_nonneg v
  rw [div_le_iff₀ (by norm_num)]
  refine (le_abs_self _).trans ((root_sum_bound
    (c := n1 u * n1 v * ((a * n1 q / 2) ^ 3 / 16)) fun r _ => ?_).trans (le_of_eq (by ring)))
  rw [abs_of_nonneg (by positivity)]
  gcongr
  · exact rk_le r u
  · exact rk_le r v
  · exact hx_le ha r q

end PMAction.PolarizationMagnitudes
