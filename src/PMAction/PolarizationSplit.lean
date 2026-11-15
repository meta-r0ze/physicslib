import PMAction.PolarizationTaylor

/-!
# Step (ii.b) of the subtracted lattice polarization: the ingredients to second order in `q`

`PolarizationTaylor` expands each root's factor to second order in `x_r = a r·q/2`. Summed over the
`D₄` roots, with `A_r = a r·k`:

* `leg_split`: `leg = (Σ_r (r·u)(sin A_r + x_r cos A_r − (2/3) x_r² sin A_r))/(6a)` up to
  `(Σ_r |r·u| |x_r|³/2)/(6a)`.
* `dS_split`: `S(k + q) − S(k) = (Σ_r 2 (x_r sin A_r + x_r² cos A_r))/(6a²)` up to
  `(Σ_r 3|x_r|³)/(6a²)` (from the exact Ward identity `FiniteVertex.ward`).
* `contact_split`: `contact = (Σ_r (r·u)(r·v) cos A_r (1 − x_r²/3))/6` up to
  `(Σ_r |r·u||r·v| |x_r|³/16)/6`.

All three need `|x_r| ≤ 1` for every root (`2|q| ≤ lo`, `a·hi ≤ 1` give it on the shell). The
zeroth-, first- and second-order parts are explicit root sums; the next step compares them with the
continuum's `2k`, `q`, `0`, `2k·q`, `q²`, `2δ`, `0`.
-/

noncomputable section
namespace PMAction.PolarizationSplit
open Real D4Gauge LeadingLog FiniteVertex PolarizationContact PolarizationTaylor

/-- Root sums over a common positive denominator: a per-root bound sums. -/
theorem sum_gap {ι : Type*} (s : Finset ι) (f g h : ι → ℝ) {c : ℝ} (hc : 0 < c)
    (H : ∀ i ∈ s, |f i - g i| ≤ h i) :
    |(∑ i ∈ s, f i) / c - (∑ i ∈ s, g i) / c| ≤ (∑ i ∈ s, h i) / c := by
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hc]
  exact div_le_div_of_nonneg_right
    ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum H)) hc.le

/-- The leg to second order in `q`. -/
def legExp (a : ℝ) (k q u : Fin 4 → ℝ) : ℝ :=
  (∑ r ∈ roots, rk r u * (sin (a * rk r k) + a * rk r q / 2 * cos (a * rk r k) -
    2 / 3 * (a * rk r q / 2) ^ 2 * sin (a * rk r k))) / (6 * a)

/-- **The leg to second order.** -/
theorem leg_split {a : ℝ} (ha : 0 < a) (k q u : Fin 4 → ℝ)
    (hx : ∀ r ∈ roots, |a * rk r q / 2| ≤ 1) :
    |leg a k q u 1 - legExp a k q u| ≤
      (∑ r ∈ roots, |rk r u| * (|a * rk r q / 2| ^ 3 / 2)) / (6 * a) := by
  unfold leg legExp
  refine sum_gap _ _ _ _ (by positivity) fun r hr => ?_
  rw [one_mul, show rk r u * sinc (a * rk r q / 2) * sin (a * rk r k + a * rk r q / 2) -
      rk r u * (sin (a * rk r k) + a * rk r q / 2 * cos (a * rk r k) -
        2 / 3 * (a * rk r q / 2) ^ 2 * sin (a * rk r k)) =
      rk r u * (sinc (a * rk r q / 2) * sin (a * rk r k + a * rk r q / 2) -
        (sin (a * rk r k) + a * rk r q / 2 * cos (a * rk r k) -
          2 / 3 * (a * rk r q / 2) ^ 2 * sin (a * rk r k))) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_left (leg_root_expand _ (hx r hr)) (abs_nonneg _)

/-- The propagator shift to second order in `q`. -/
def dSExp (a : ℝ) (k q : Fin 4 → ℝ) : ℝ :=
  (∑ r ∈ roots, 2 * (a * rk r q / 2 * sin (a * rk r k) +
    (a * rk r q / 2) ^ 2 * cos (a * rk r k))) / (6 * a ^ 2)

/-- **The propagator shift to second order.** -/
theorem dS_split {a : ℝ} (ha : 0 < a) (k q : Fin 4 → ℝ)
    (hx : ∀ r ∈ roots, |a * rk r q / 2| ≤ 1) :
    |symbol a (k + q) - symbol a k - dSExp a k q| ≤
      (∑ r ∈ roots, 3 * |a * rk r q / 2| ^ 3) / (6 * a ^ 2) := by
  rw [ward, contracted, dSExp]
  refine sum_gap _ _ _ _ (by positivity) fun r hr => ?_
  rw [show 2 * sin (a * rk r k + a * rk r q / 2) * sin (a * rk r q / 2) -
      2 * (a * rk r q / 2 * sin (a * rk r k) + (a * rk r q / 2) ^ 2 * cos (a * rk r k)) =
      2 * (sin (a * rk r k + a * rk r q / 2) * sin (a * rk r q / 2) -
        (a * rk r q / 2 * sin (a * rk r k) + (a * rk r q / 2) ^ 2 * cos (a * rk r k))) by ring,
    abs_mul, abs_two]
  linarith [dS_root_expand (a * rk r k) (hx r hr)]

/-- The contact to second order in `q`. -/
def contactExp (a : ℝ) (k q u v : Fin 4 → ℝ) : ℝ :=
  (∑ r ∈ roots, rk r u * rk r v * (cos (a * rk r k) * (1 - (a * rk r q / 2) ^ 2 / 3))) / 6

/-- **The contact to second order.** -/
theorem contact_split (a : ℝ) (k q u v : Fin 4 → ℝ)
    (hx : ∀ r ∈ roots, |a * rk r q / 2| ≤ 1) :
    |contact a k q u v - contactExp a k q u v| ≤
      (∑ r ∈ roots, |rk r u| * |rk r v| * (|a * rk r q / 2| ^ 3 / 16)) / 6 := by
  unfold contact contactExp
  refine sum_gap _ _ _ _ (by norm_num) fun r hr => ?_
  rw [show cos (a * rk r k) * (rk r u * sinc (a * rk r q / 2)) * (rk r v * sinc (a * rk r q / 2)) -
      rk r u * rk r v * (cos (a * rk r k) * (1 - (a * rk r q / 2) ^ 2 / 3)) =
      rk r u * rk r v * (cos (a * rk r k) * sinc (a * rk r q / 2) ^ 2 -
        cos (a * rk r k) * (1 - (a * rk r q / 2) ^ 2 / 3)) by ring, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (contact_root_expand _ (hx r hr)) (by positivity)

end PMAction.PolarizationSplit
