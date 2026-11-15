import PMAction.PolarizationPointwise
import PMAction.ShellMoments

/-!
# Step (d1) of the subtracted lattice polarization: the pointwise bound on the Euclidean shell

`PolarizationPointwise.pointwise` holds under conditions on `κ = n(k)`, `t = n(q)` and the symbols.
On the shell `lo < |k| < hi` of `ShellMoments` (momenta in `EuclideanSpace`, `LeadingLog.Mom`), with
`4|q| ≤ lo` and `2 a hi ≤ 1`, those conditions hold:

* `sq4_le_n1`, `n1_le_sq4`: `|w|² ≤ n(w)² ≤ 4|w|²`;
* the symbol at `k ± q`: `|k ± q| ≥ 3|k|/4`, so `S(k ± q) ≥ 9|k|²/32 ≥ κ²/16` (`half_le_symbol`);
* `coefC_eq_Q`: the continuum's second order `Q` at `S = |k|²` is `ShellMoments.coefC`.

* `shell_pointwise`: for `k` on the shell,
  `|(L(q) + L(−q))/2 − L(0) − coefC q μ ν k| ≤ (4K a² hi² |q|² + 8P(1) |q|³/lo) |k|⁻⁴`,
  with `K = 271853128/3`, `P(1) = 47979504985/36` (`PolarizationShellQ`, `PolarizationShellCubic`).
-/

noncomputable section
namespace PMAction.PolarizationShellPointwise
open Real MeasureTheory LeadingLog PolarizationContact PolarizationOrders PolarizationMagnitudes
  PolarizationAssembly PolarizationPointwise ShellMoments

lemma sq4_le_n1 (w : Fin 4 → ℝ) : sq4 w ≤ n1 w ^ 2 := by
  simp only [sq4, n1, Fin.sum_univ_four]
  have := abs_nonneg (w 0); have := abs_nonneg (w 1); have := abs_nonneg (w 2)
  have := abs_nonneg (w 3)
  rw [← sq_abs (w 0), ← sq_abs (w 1), ← sq_abs (w 2), ← sq_abs (w 3)]
  nlinarith [mul_nonneg (abs_nonneg (w 0)) (abs_nonneg (w 1)),
    mul_nonneg (abs_nonneg (w 0)) (abs_nonneg (w 2)), mul_nonneg (abs_nonneg (w 0)) (abs_nonneg (w 3)),
    mul_nonneg (abs_nonneg (w 1)) (abs_nonneg (w 2)), mul_nonneg (abs_nonneg (w 1)) (abs_nonneg (w 3)),
    mul_nonneg (abs_nonneg (w 2)) (abs_nonneg (w 3))]

lemma n1_le_sq4 (w : Fin 4 → ℝ) : n1 w ^ 2 ≤ 4 * sq4 w := by
  simp only [sq4, n1, Fin.sum_univ_four]
  rw [← sq_abs (w 0), ← sq_abs (w 1), ← sq_abs (w 2), ← sq_abs (w 3)]
  nlinarith [sq_nonneg (|w 0| - |w 1|), sq_nonneg (|w 0| - |w 2|), sq_nonneg (|w 0| - |w 3|),
    sq_nonneg (|w 1| - |w 2|), sq_nonneg (|w 1| - |w 3|), sq_nonneg (|w 2| - |w 3|)]

lemma le_of_sq_le {x y : ℝ} (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

lemma sq4_mom (k : Mom) : sq4 (fun i => k i) = ‖k‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq k).symm

lemma inner_eq_dot (k q : Mom) :
    inner ℝ k q = PolarizationOrders.dot (fun i => q i) (fun i => k i) := by
  simp [PiLp.inner_apply, PolarizationOrders.dot, mul_comm]

/-- **The continuum's second order is `coefC`.** -/
theorem coefC_eq_Q (q k : Mom) (μ ν : Fin 4) (hk : k ≠ 0) :
    coefC q μ ν k = Q (sq4 (fun i => k i)) (2 * k μ) (q μ) 0 (2 * k ν) (q ν) 0
      (2 * PolarizationOrders.dot (fun i => q i) (fun i => k i))
      (PolarizationOrders.dot (fun i => q i) (fun i => q i)) 0 := by
  have hn : 0 < ‖k‖ := norm_pos_iff.2 hk
  have hqq : PolarizationOrders.dot (fun i => q i) (fun i => q i) = ‖q‖ ^ 2 := by
    rw [← sq4_mom q]; simp [PolarizationOrders.dot, sq4, sq]
  rw [sq4_mom, hqq, ← inner_eq_dot]
  unfold coefC Q
  field_simp
  ring

/-- **The pointwise bound on the shell.** -/
theorem shell_pointwise {a lo hi : ℝ} (ha : 0 < a) (hlo : 0 < lo) (hah : 2 * a * hi ≤ 1)
    {q : Mom} (hq : 4 * ‖q‖ ≤ lo) {k : Mom} (hk : k ∈ shell lo hi) (μ ν : Fin 4) :
    |(latInt a (fun i => q i) μ ν (fun i => k i) + latInt a (-(fun i => q i)) μ ν (fun i => k i)) / 2 -
        latInt a 0 μ ν (fun i => k i) - coefC q μ ν k| ≤
      (4 * (271853128 / 3) * a ^ 2 * hi ^ 2 * ‖q‖ ^ 2 + 8 * (47979504985 / 36) * ‖q‖ ^ 3 / lo) *
        ‖k‖⁻¹ ^ 4 := by
  obtain ⟨hk1, hk2⟩ : lo < ‖k‖ ∧ ‖k‖ < hi := by simpa [shell] using hk
  have hr : 0 < ‖k‖ := hlo.trans hk1
  have hk0 : k ≠ 0 := norm_pos_iff.1 hr
  have hq0 := norm_nonneg q
  have hK := sq4_mom k
  have hQ := sq4_mom q
  have hκr2 : ‖k‖ ^ 2 ≤ n1 (fun i => k i) ^ 2 := hK ▸ sq4_le_n1 _
  have hκ2 : n1 (fun i => k i) ^ 2 ≤ 4 * ‖k‖ ^ 2 := hK ▸ n1_le_sq4 _
  have hκr : ‖k‖ ≤ n1 (fun i => k i) := le_of_sq_le (n1_nonneg _) hκr2
  have hκ : 0 < n1 (fun i => k i) := hr.trans_le hκr
  have hκle : n1 (fun i => k i) ≤ 2 * ‖k‖ := le_of_sq_le (by positivity) (by nlinarith)
  have ht2 : n1 (fun i => q i) ^ 2 ≤ 4 * ‖q‖ ^ 2 := hQ ▸ n1_le_sq4 _
  have htq : n1 (fun i => q i) ≤ 2 * ‖q‖ := le_of_sq_le (by positivity) (by nlinarith)
  have ht : n1 (fun i => q i) ≤ n1 (fun i => k i) := by linarith
  have haκ : a * n1 (fun i => k i) ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hκle ha.le]
  have hhi : 0 < hi := hr.trans hk2
  have hah2 : a ^ 2 * (4 * hi ^ 2) ≤ 1 := by
    have h0 : 0 ≤ 2 * a * hi := by positivity
    calc a ^ 2 * (4 * hi ^ 2) = (2 * a * hi) ^ 2 := by ring
      _ ≤ 1 := pow_le_one₀ h0 hah
  have h6 : a ^ 2 * sq4 (fun i => k i) ≤ 6 := by rw [hK]; nlinarith
  -- the symbol at k
  have hS : n1 (fun i => k i) ^ 2 / 8 ≤ symbol a (fun i => k i) := by
    have := half_le_symbol ha h6; rw [hK] at this; linarith
  have hSle : symbol a (fun i => k i) ≤ n1 (fun i => k i) ^ 2 := by
    have := symbol_le ha (fun i => k i); rw [hK] at this; linarith
  have hSc : n1 (fun i => k i) ^ 2 / 8 ≤ sq4 (fun i => k i) := by rw [hK]; linarith
  have hScle : sq4 (fun i => k i) ≤ n1 (fun i => k i) ^ 2 := by rw [hK]; exact hκr2
  have hdS : |symbol a (fun i => k i) - sq4 (fun i => k i)| ≤ a ^ 2 * n1 (fun i => k i) ^ 4 / 12 := by
    obtain ⟨g1, g2⟩ := symbol_gap ha (fun i => k i)
    rw [abs_sub_comm, abs_of_nonneg g1]
    refine g2.trans ?_
    have : sq4 (fun i => k i) ^ 2 ≤ n1 (fun i => k i) ^ 4 := by
      rw [show n1 (fun i => k i) ^ 4 = (n1 (fun i => k i) ^ 2) ^ 2 by ring]
      exact pow_le_pow_left₀ (by rw [hK]; positivity) hScle 2
    nlinarith [sq_nonneg a]
  -- the symbol at k ± q
  have side : ∀ p : Mom, ‖p‖ ≤ ‖q‖ →
      n1 (fun i => k i) ^ 2 / 16 ≤ symbol a (fun i => (k + p) i) := by
    intro p hp
    have hl : ‖k‖ - ‖p‖ ≤ ‖k + p‖ := by
      have := norm_sub_norm_le k (-p); rwa [norm_neg, sub_neg_eq_add] at this
    have hu : ‖k + p‖ ≤ ‖k‖ + ‖p‖ := norm_add_le _ _
    have hsq := sq4_mom (k + p)
    have h6' : a ^ 2 * sq4 (fun i => (k + p) i) ≤ 6 := by
      rw [hsq]
      have h2 : ‖k + p‖ ≤ 2 * hi := by linarith
      have : ‖k + p‖ ^ 2 ≤ 4 * hi ^ 2 := by nlinarith [norm_nonneg (k + p)]
      nlinarith
    have := half_le_symbol ha h6'
    rw [hsq] at this
    have h34 : 3 / 4 * ‖k‖ ≤ ‖k + p‖ := by linarith
    have : (3 / 4 * ‖k‖) ^ 2 ≤ ‖k + p‖ ^ 2 := pow_le_pow_left₀ (by positivity) h34 2
    nlinarith
  have hSq : n1 (fun i => k i) ^ 2 / 16 ≤ symbol a ((fun i => k i) + fun i => q i) := by
    have := side q le_rfl
    rwa [show (fun i => (k + q) i) = (fun i => k i) + fun i => q i by funext i; simp] at this
  have hSmq : n1 (fun i => k i) ^ 2 / 16 ≤ symbol a ((fun i => k i) + -fun i => q i) := by
    have := side (-q) (by rw [norm_neg])
    rwa [show (fun i => (k + -q) i) = (fun i => k i) + -fun i => q i by funext i; simp] at this
  have hp := pointwise μ ν ha hκ ht haκ hS hSle hSq hSmq hSc hScle hdS
  have e := coefC_eq_Q q k μ ν hk0
  beta_reduce at hp e ⊢
  -- to the |k|⁻⁴ form
  have e1 : 271853128 / 3 * a ^ 2 * n1 (fun i => q i) ^ 2 / n1 (fun i => k i) ^ 2 ≤
      4 * (271853128 / 3) * a ^ 2 * hi ^ 2 * ‖q‖ ^ 2 / ‖k‖ ^ 4 := by
    rw [div_le_div_iff₀ (pow_pos hκ 2) (pow_pos hr 4)]
    have hr4 : ‖k‖ ^ 4 ≤ hi ^ 2 * n1 (fun i => k i) ^ 2 := by
      have : ‖k‖ ^ 2 ≤ hi ^ 2 := pow_le_pow_left₀ hr.le hk2.le 2
      exact (mul_le_mul this hκr2 (sq_nonneg _) (sq_nonneg _)).trans' (le_of_eq (by ring))
    have h4 := mul_le_mul ht2 hr4 (by positivity) (by positivity)
    have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 271853128 / 3 * a ^ 2)
    calc 271853128 / 3 * a ^ 2 * n1 (fun i => q i) ^ 2 * ‖k‖ ^ 4
        = 271853128 / 3 * a ^ 2 * (n1 (fun i => q i) ^ 2 * ‖k‖ ^ 4) := by ring
      _ ≤ 271853128 / 3 * a ^ 2 * (4 * ‖q‖ ^ 2 * (hi ^ 2 * n1 (fun i => k i) ^ 2)) := h5
      _ = 4 * (271853128 / 3) * a ^ 2 * hi ^ 2 * ‖q‖ ^ 2 * n1 (fun i => k i) ^ 2 := by ring
  have e2 : 47979504985 / 36 * n1 (fun i => q i) ^ 3 / n1 (fun i => k i) ^ 5 ≤
      8 * (47979504985 / 36) * ‖q‖ ^ 3 / lo / ‖k‖ ^ 4 := by
    rw [div_div, div_le_div_iff₀ (pow_pos hκ 5) (mul_pos hlo (pow_pos hr 4))]
    have ht3 : n1 (fun i => q i) ^ 3 ≤ 8 * ‖q‖ ^ 3 := by
      exact (pow_le_pow_left₀ (n1_nonneg _) htq 3).trans (le_of_eq (by ring))
    have hr5 : lo * ‖k‖ ^ 4 ≤ n1 (fun i => k i) ^ 5 := by
      have h1 : lo * ‖k‖ ^ 4 ≤ ‖k‖ ^ 5 :=
        (mul_le_mul_of_nonneg_right hk1.le (pow_pos hr 4).le).trans (le_of_eq (by ring))
      exact h1.trans (pow_le_pow_left₀ hr.le hκr 5)
    have h4 := mul_le_mul ht3 hr5 (mul_pos hlo (pow_pos hr 4)).le (by positivity)
    have h5 := mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 47979504985 / 36)
    calc 47979504985 / 36 * n1 (fun i => q i) ^ 3 * (lo * ‖k‖ ^ 4)
        = 47979504985 / 36 * (n1 (fun i => q i) ^ 3 * (lo * ‖k‖ ^ 4)) := by ring
      _ ≤ 47979504985 / 36 * (8 * ‖q‖ ^ 3 * n1 (fun i => k i) ^ 5) := h5
      _ = 8 * (47979504985 / 36) * ‖q‖ ^ 3 * n1 (fun i => k i) ^ 5 := by ring
  have hinv : ‖k‖⁻¹ ^ 4 = 1 / ‖k‖ ^ 4 := by rw [inv_pow, one_div]
  rw [hinv]
  have := abs_le.1 hp
  refine abs_le.2 ⟨?_, ?_⟩
  · have : (4 * (271853128 / 3) * a ^ 2 * hi ^ 2 * ‖q‖ ^ 2 + 8 * (47979504985 / 36) * ‖q‖ ^ 3 / lo) *
        (1 / ‖k‖ ^ 4) = 4 * (271853128 / 3) * a ^ 2 * hi ^ 2 * ‖q‖ ^ 2 / ‖k‖ ^ 4 +
          8 * (47979504985 / 36) * ‖q‖ ^ 3 / lo / ‖k‖ ^ 4 := by ring
    rw [this]; linarith
  · have : (4 * (271853128 / 3) * a ^ 2 * hi ^ 2 * ‖q‖ ^ 2 + 8 * (47979504985 / 36) * ‖q‖ ^ 3 / lo) *
        (1 / ‖k‖ ^ 4) = 4 * (271853128 / 3) * a ^ 2 * hi ^ 2 * ‖q‖ ^ 2 / ‖k‖ ^ 4 +
          8 * (47979504985 / 36) * ‖q‖ ^ 3 / lo / ‖k‖ ^ 4 := by ring
    rw [this]; linarith

end PMAction.PolarizationShellPointwise
