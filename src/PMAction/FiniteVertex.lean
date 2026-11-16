import PMAction.PolarizationAverage

/-!
# The finite-`q` current vertex of the link Laplacian: Ward identity and midpoint gap

`PolarizationAverage.vertex_gap` controls `∂_μ symbol` at one momentum `w`. A polarization loop needs
the vertex between `k` and `k + q`. The gauged hop fixes it through the Ward identity: its
contraction with `q` is the difference of inverse propagators.

* `ward`: exactly, `symbol(k + q) − symbol(k) = Σ_r 2 sin(a r·(k + q/2)) sin(a r·q/2) / (6a²)`.
  So the conserved vertex is the midpoint vertex `∂ symbol(k + q/2)` with each root weighted by
  `sin x / x`, `x = a r·q/2`.
* `contract_vertex`: `q · ∂ symbol(w) = Σ_r (r·q) sin(a r·w) / (6a)`.
* `root_gap`, `midpoint_gap`: the midpoint vertex alone misses the Ward identity by at most
  `a²/144 · Σ_r |r·w| |r·q|³`, `w = k + q/2`: `O(a²|k||q|³)`.

So inserting `w = k + q/2` into `vertex_gap` is not the physical finite-`q` vertex; the difference is
`O(a² q²)` relative per root, which survives as `O(a²)` in the `q²` coefficient and must be carried
in the subtracted lattice polarization (`REVIEW-AND-NEXT.md`). The two-field contact (seagull) term
and its longitudinal Ward identity are derived in `PolarizationContact`; the wrapped finite-grid
cancellation and longitudinal regulator limit are in `FinitePolarization`.
-/

noncomputable section
namespace PMAction.FiniteVertex
open Real D4Gauge LeadingLog PolarizationAverage

lemma rk_add (r : Fin 4 → Fin 3) (k q : Fin 4 → ℝ) : rk r (k + q) = rk r k + rk r q := by
  simp only [rk, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma rk_mid (r : Fin 4 → Fin 3) (k q : Fin 4 → ℝ) :
    rk r (fun i => k i + q i / 2) = rk r k + rk r q / 2 := by
  simp only [rk, mul_add, Finset.sum_add_distrib, Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The exact contraction of the finite-`q` vertex with `q`. -/
def contracted (a : ℝ) (k q : Fin 4 → ℝ) : ℝ :=
  (∑ r ∈ roots, 2 * sin (a * rk r k + a * rk r q / 2) * sin (a * rk r q / 2)) / (6 * a ^ 2)

/-- **Ward identity.** The difference of inverse propagators is the contracted vertex. -/
theorem ward (a : ℝ) (k q : Fin 4 → ℝ) : symbol a (k + q) - symbol a k = contracted a k q := by
  rw [symbol, symbol, contracted, ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [rk_add, sub_sub_sub_cancel_left, Real.cos_sub_cos]
  have h1 : (a * rk r k + a * (rk r k + rk r q)) / 2 = a * rk r k + a * rk r q / 2 := by ring
  have h2 : (a * rk r k - a * (rk r k + rk r q)) / 2 = -(a * rk r q / 2) := by ring
  rw [h1, h2, Real.sin_neg]
  ring

/-- **`q · ∂ symbol(w)`** as a root sum. -/
theorem contract_vertex (a : ℝ) (w q : Fin 4 → ℝ) :
    ∑ μ, q μ * vertex a w μ = (∑ r ∈ roots, rk r q * sin (a * rk r w)) / (6 * a) := by
  simp only [vertex, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [rk, Finset.sum_mul, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **One root's Ward gap.** -/
theorem root_gap {a : ℝ} (ha : 0 < a) (W Q : ℝ) :
    |2 * sin (a * W) * sin (a * Q / 2) / (6 * a ^ 2) - Q * sin (a * W) / (6 * a)| ≤
      a ^ 2 * |W| * |Q| ^ 3 / 144 := by
  have ha0 : a ≠ 0 := ha.ne'
  have e : 2 * sin (a * W) * sin (a * Q / 2) / (6 * a ^ 2) - Q * sin (a * W) / (6 * a) =
      2 * sin (a * W) * (sin (a * Q / 2) - a * Q / 2) / (6 * a ^ 2) := by
    field_simp
  have h1 : |sin (a * W)| ≤ |a * W| := Real.abs_sin_le_abs
  have h2 : |sin (a * Q / 2) - a * Q / 2| ≤ |a * Q / 2| ^ 3 / 6 := by
    rw [abs_sub_comm]; exact abs_sub_sin_le _
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 6 * a ^ 2), div_le_iff₀ (by positivity)]
  calc |2 * sin (a * W) * (sin (a * Q / 2) - a * Q / 2)|
        = 2 * |sin (a * W)| * |sin (a * Q / 2) - a * Q / 2| := by
          rw [abs_mul, abs_mul, abs_two]
    _ ≤ 2 * |a * W| * (|a * Q / 2| ^ 3 / 6) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (abs_nonneg _)
            (by positivity)
    _ = a ^ 2 * |W| * |Q| ^ 3 / 144 * (6 * a ^ 2) := by
          simp only [abs_mul, abs_div, abs_of_pos ha, abs_two]; ring

/-- **The midpoint vertex misses the Ward identity by `O(a²|k||q|³)`.** -/
theorem midpoint_gap {a : ℝ} (ha : 0 < a) (k q : Fin 4 → ℝ) :
    |symbol a (k + q) - symbol a k - ∑ μ, q μ * vertex a (fun i => k i + q i / 2) μ| ≤
      a ^ 2 / 144 * ∑ r ∈ roots, |rk r (fun i => k i + q i / 2)| * |rk r q| ^ 3 := by
  rw [ward, contract_vertex, contracted, Finset.sum_div, Finset.sum_div,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  have hm : a * rk r k + a * rk r q / 2 = a * rk r (fun i => k i + q i / 2) := by
    rw [rk_mid]; ring
  rw [hm]
  calc _ ≤ a ^ 2 * |rk r (fun i => k i + q i / 2)| * |rk r q| ^ 3 / 144 := root_gap ha _ _
    _ = _ := by ring

end PMAction.FiniteVertex
