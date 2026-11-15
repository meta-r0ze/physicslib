import PMAction.PolarizationSplit

/-!
# Step (ii.c) of the subtracted lattice polarization: each order against the continuum

`PolarizationSplit` writes the leg, the propagator shift and the contact as explicit root sums to
second order in `x_r = a r·q/2`, with `A_r = a r·k`. Split by order:

* leg: `l0 = Σ(r·u) sin A/(6a)`, `l1 = Σ(r·u) x cos A/(6a)`, `l2 = Σ(r·u)(−⅔x² sin A)/(6a)`
  (`legExp_eq`);
* propagator shift: `s1 = Σ 2x sin A/(6a²)`, `s2 = Σ 2x² cos A/(6a²)` (`dSExp_eq`);
* contact: `c0 = Σ(r·u)(r·v) cos A/6`, `c2 = Σ(r·u)(r·v) cos A (−x²/3)/6` (`contactExp_eq`).

Each against its continuum root sum (`*_gap`), per root by `|sin A − A| ≤ |A|³/6`,
`|cos A − 1| ≤ A²/2`, `|sin A| ≤ |A|`; every error carries `a²` once `A = a r·k`, `x = a r·q/2` are
inserted. The continuum root sums are the continuum's values (`root_dot`:
`Σ_r (r·u)(r·w) = 12 u·w`): `l0 → 2k·u`, `l1 → q·u`, `l2 → 0`, `s1 → 2k·q`, `s2 → q·q`,
`c0 → 2u·v`, `c2 → 0` (`conv_*`).
-/

noncomputable section
namespace PMAction.PolarizationOrders
open Real D4Gauge LeadingLog PolarizationSplit

/-- The Euclidean dot product on `Fin 4 → ℝ`. -/
def dot (u w : Fin 4 → ℝ) : ℝ := ∑ i, u i * w i

/-- **The `D₄` root sum of a product of projections is `12` times the dot product.** -/
lemma root_dot (u w : Fin 4 → ℝ) : ∑ r ∈ roots, rk r u * rk r w = 12 * dot u w := by
  have h : ∀ r, rk r u * rk r w = ∑ i, u i * (rk r w * vec r i) := fun r => by
    rw [rk, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun r _ => h r, Finset.sum_comm]
  simp only [← Finset.mul_sum, cross_moment]
  rw [dot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma abs_cos_sub_one (A : ℝ) : |cos A - 1| ≤ A ^ 2 / 2 := by
  rw [abs_sub_comm, abs_of_nonneg (by linarith [cos_le_one A])]
  linarith [one_sub_sq_div_two_le_cos (x := A)]

/-! ## The orders -/

def l0 (a : ℝ) (k u : Fin 4 → ℝ) : ℝ := (∑ r ∈ roots, rk r u * sin (a * rk r k)) / (6 * a)
def l1 (a : ℝ) (k q u : Fin 4 → ℝ) : ℝ :=
  (∑ r ∈ roots, rk r u * (a * rk r q / 2 * cos (a * rk r k))) / (6 * a)
def l2 (a : ℝ) (k q u : Fin 4 → ℝ) : ℝ :=
  (∑ r ∈ roots, rk r u * (-(2 / 3 * (a * rk r q / 2) ^ 2 * sin (a * rk r k)))) / (6 * a)
def s1 (a : ℝ) (k q : Fin 4 → ℝ) : ℝ :=
  (∑ r ∈ roots, 2 * (a * rk r q / 2 * sin (a * rk r k))) / (6 * a ^ 2)
def s2 (a : ℝ) (k q : Fin 4 → ℝ) : ℝ :=
  (∑ r ∈ roots, 2 * ((a * rk r q / 2) ^ 2 * cos (a * rk r k))) / (6 * a ^ 2)
def c0 (a : ℝ) (k u v : Fin 4 → ℝ) : ℝ :=
  (∑ r ∈ roots, rk r u * rk r v * cos (a * rk r k)) / 6
def c2 (a : ℝ) (k q u v : Fin 4 → ℝ) : ℝ :=
  (∑ r ∈ roots, rk r u * rk r v * (cos (a * rk r k) * (-((a * rk r q / 2) ^ 2 / 3)))) / 6

theorem legExp_eq (a : ℝ) (k q u : Fin 4 → ℝ) :
    legExp a k q u = l0 a k u + l1 a k q u + l2 a k q u := by
  unfold legExp l0 l1 l2
  rw [← add_div, ← add_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1; exact Finset.sum_congr rfl fun r _ => by ring

theorem dSExp_eq (a : ℝ) (k q : Fin 4 → ℝ) : dSExp a k q = s1 a k q + s2 a k q := by
  unfold dSExp s1 s2
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1; exact Finset.sum_congr rfl fun r _ => by ring

theorem contactExp_eq (a : ℝ) (k q u v : Fin 4 → ℝ) :
    contactExp a k q u v = c0 a k u v + c2 a k q u v := by
  unfold contactExp c0 c2
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1; exact Finset.sum_congr rfl fun r _ => by ring

/-! ## Each order against its continuum root sum -/

theorem l0_gap {a : ℝ} (ha : 0 < a) (k u : Fin 4 → ℝ) :
    |l0 a k u - (∑ r ∈ roots, rk r u * (a * rk r k)) / (6 * a)| ≤
      (∑ r ∈ roots, |rk r u| * (|a * rk r k| ^ 3 / 6)) / (6 * a) := by
  refine sum_gap _ _ _ _ (by positivity) fun r _ => ?_
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact abs_sub_sin_le _) (abs_nonneg _)

theorem l1_gap {a : ℝ} (ha : 0 < a) (k q u : Fin 4 → ℝ) :
    |l1 a k q u - (∑ r ∈ roots, rk r u * (a * rk r q / 2)) / (6 * a)| ≤
      (∑ r ∈ roots, |rk r u| * (|a * rk r q / 2| * ((a * rk r k) ^ 2 / 2))) / (6 * a) := by
  refine sum_gap _ _ _ _ (by positivity) fun r _ => ?_
  rw [← mul_sub, abs_mul,
    show a * rk r q / 2 * cos (a * rk r k) - a * rk r q / 2 =
      a * rk r q / 2 * (cos (a * rk r k) - 1) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (abs_cos_sub_one _) (abs_nonneg _)) (abs_nonneg _)

theorem l2_gap {a : ℝ} (ha : 0 < a) (k q u : Fin 4 → ℝ) :
    |l2 a k q u - (∑ _r ∈ roots, (0 : ℝ)) / (6 * a)| ≤
      (∑ r ∈ roots, |rk r u| * (2 / 3 * (a * rk r q / 2) ^ 2 * |a * rk r k|)) / (6 * a) := by
  refine sum_gap _ _ _ _ (by positivity) fun r _ => ?_
  rw [sub_zero, abs_mul, abs_neg, abs_mul, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ 2 / 3 * (a * rk r q / 2) ^ 2)]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by positivity)) (abs_nonneg _)

theorem s1_gap {a : ℝ} (ha : 0 < a) (k q : Fin 4 → ℝ) :
    |s1 a k q - (∑ r ∈ roots, 2 * (a * rk r q / 2 * (a * rk r k))) / (6 * a ^ 2)| ≤
      (∑ r ∈ roots, 2 * (|a * rk r q / 2| * (|a * rk r k| ^ 3 / 6))) / (6 * a ^ 2) := by
  refine sum_gap _ _ _ _ (by positivity) fun r _ => ?_
  rw [← mul_sub, ← mul_sub, abs_mul, abs_two, abs_mul]
  gcongr
  rw [abs_sub_comm]; exact abs_sub_sin_le _

theorem s2_gap {a : ℝ} (ha : 0 < a) (k q : Fin 4 → ℝ) :
    |s2 a k q - (∑ r ∈ roots, 2 * (a * rk r q / 2) ^ 2) / (6 * a ^ 2)| ≤
      (∑ r ∈ roots, 2 * ((a * rk r q / 2) ^ 2 * ((a * rk r k) ^ 2 / 2))) / (6 * a ^ 2) := by
  refine sum_gap _ _ _ _ (by positivity) fun r _ => ?_
  rw [show 2 * ((a * rk r q / 2) ^ 2 * cos (a * rk r k)) - 2 * (a * rk r q / 2) ^ 2 =
      2 * ((a * rk r q / 2) ^ 2 * (cos (a * rk r k) - 1)) by ring, abs_mul, abs_two, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a * rk r q / 2) ^ 2)]
  gcongr
  exact abs_cos_sub_one _

theorem c0_gap (a : ℝ) (k u v : Fin 4 → ℝ) :
    |c0 a k u v - (∑ r ∈ roots, rk r u * rk r v) / 6| ≤
      (∑ r ∈ roots, |rk r u| * |rk r v| * ((a * rk r k) ^ 2 / 2)) / 6 := by
  refine sum_gap _ _ _ _ (by norm_num) fun r _ => ?_
  rw [show rk r u * rk r v * cos (a * rk r k) - rk r u * rk r v =
      rk r u * rk r v * (cos (a * rk r k) - 1) by ring, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_cos_sub_one _) (by positivity)

theorem c2_gap (a : ℝ) (k q u v : Fin 4 → ℝ) :
    |c2 a k q u v - (∑ _r ∈ roots, (0 : ℝ)) / 6| ≤
      (∑ r ∈ roots, |rk r u| * |rk r v| * ((a * rk r q / 2) ^ 2 / 3)) / 6 := by
  refine sum_gap _ _ _ _ (by norm_num) fun r _ => ?_
  rw [sub_zero, abs_mul, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a * rk r q / 2) ^ 2 / 3)]
  calc |rk r u| * |rk r v| * (|cos (a * rk r k)| * ((a * rk r q / 2) ^ 2 / 3))
      ≤ |rk r u| * |rk r v| * (1 * ((a * rk r q / 2) ^ 2 / 3)) := by
        gcongr; exact abs_cos_le_one _
    _ = _ := by ring

/-! ## The continuum root sums are the continuum's values -/

theorem conv_l0 {a : ℝ} (ha : 0 < a) (k u : Fin 4 → ℝ) :
    (∑ r ∈ roots, rk r u * (a * rk r k)) / (6 * a) = 2 * dot u k := by
  rw [show (∑ r ∈ roots, rk r u * (a * rk r k)) = a * ∑ r ∈ roots, rk r u * rk r k by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring, root_dot]
  field_simp
  try ring

theorem conv_l1 {a : ℝ} (ha : 0 < a) (q u : Fin 4 → ℝ) :
    (∑ r ∈ roots, rk r u * (a * rk r q / 2)) / (6 * a) = dot u q := by
  rw [show (∑ r ∈ roots, rk r u * (a * rk r q / 2)) = a / 2 * ∑ r ∈ roots, rk r u * rk r q by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring, root_dot]
  field_simp
  try ring

theorem conv_s1 {a : ℝ} (ha : 0 < a) (k q : Fin 4 → ℝ) :
    (∑ r ∈ roots, 2 * (a * rk r q / 2 * (a * rk r k))) / (6 * a ^ 2) = 2 * dot q k := by
  rw [show (∑ r ∈ roots, 2 * (a * rk r q / 2 * (a * rk r k))) =
      a ^ 2 * ∑ r ∈ roots, rk r q * rk r k by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring, root_dot]
  field_simp
  try ring

theorem conv_s2 {a : ℝ} (ha : 0 < a) (q : Fin 4 → ℝ) :
    (∑ r ∈ roots, 2 * (a * rk r q / 2) ^ 2) / (6 * a ^ 2) = dot q q := by
  rw [show (∑ r ∈ roots, 2 * (a * rk r q / 2) ^ 2) = a ^ 2 / 2 * ∑ r ∈ roots, rk r q * rk r q by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring, root_dot]
  field_simp
  try ring

theorem conv_c0 (u v : Fin 4 → ℝ) : (∑ r ∈ roots, rk r u * rk r v) / 6 = 2 * dot u v := by
  rw [root_dot]; ring

end PMAction.PolarizationOrders
