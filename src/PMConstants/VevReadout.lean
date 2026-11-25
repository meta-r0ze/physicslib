import PMConstants.NoiseShare
import PMConstants.RepairBudget

/-!
# The VEV corrections as one exact repair, read out once

Returning each displacement exactly gives the linear factor `1 + x`.
If a repair instead leaves a residual fraction `r`, the geometric sum
of repairs is `1 + x/(1 − r)`. Equal partial repairs satisfy the lower
bound in `compound_lower`.

Exact repair clears the reference's time axis, and symmetry makes the
three spatial shares equal (`NoiseShare.share_spatial`). Every normalized
spatial readout therefore gives `Y/3`. Adding time-axis weight `w₀` gives
`(1 − w₀)Y/3`, including `Y/4` for uniform weights over all four axes.
The link-hop readout uses spatial weights.
-/

noncomputable section
namespace PMConstants.VevReadout
open PMConstants VevCorrections

/-- **An exact repair's net correction is the displacement itself.** -/
theorem exact_net_is_identity {Dsp T : Type*} [AddGroup Dsp] (prepare : Dsp → T) (run : T → T)
    (observe : T → Dsp) (hexact : ∀ d, observe (run (prepare d)) = 0) :
    (fun d => d - observe (run (prepare d))) = id := by
  funext d; simp [hexact d]

/-- Correction factor with residual fraction `r` re-repaired: `1 + x (1 + r + r² + …)`. -/
theorem residual_series (x r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun k : ℕ => x * r ^ k) (x / (1 - r)) ∧
      (r = 0 → 1 + x / (1 - r) = 1 + x) ∧ (r = x → x < 1 → 1 + x / (1 - r) = 1 / (1 - x)) := by
  refine ⟨?_, fun h => by simp [h], fun h hx => ?_⟩
  · have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left x
    simpa [div_eq_mul_inv] using this
  · subst h
    have : (1 : ℝ) - r ≠ 0 := by linarith
    field_simp; ring

/-- Quadratic Bernoulli bound. -/
lemma pow_quadratic (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    1 + n * t + (n * (n - 1) / 2) * t ^ 2 ≤ (1 + t) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (1 + t)]
    have h1 : 0 ≤ (1 + t) := by linarith
    have hn : (0:ℝ) ≤ n * (n - 1) := by
      rcases n with _ | n
      · simp
      · push_cast; nlinarith
    have hc : 0 ≤ (n * (n - 1) / 2 : ℝ) * t ^ 3 := by positivity
    have hm := mul_le_mul_of_nonneg_right ih h1
    push_cast
    nlinarith [hm, hc, sq_nonneg t]

/-- **`n ≥ 2` equal partial repairs exceed `1 + x + x²/4`.** -/
theorem compound_lower (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (hn : 2 ≤ n) :
    1 + x + x ^ 2 / 4 ≤ (1 + x / n) ^ n := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h := pow_quadratic (x / n) (by positivity) n
  have e1 : (n : ℝ) * (x / n) = x := by field_simp
  have e2 : ((n : ℝ) * (n - 1) / 2) * (x / n) ^ 2 = (n - 1) / (2 * n) * x ^ 2 := by
    field_simp
  have e3 : (1 : ℝ) / 4 ≤ (n - 1) / (2 * n) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  nlinarith [mul_le_mul_of_nonneg_right e3 (sq_nonneg x)]

/-- **Any normalized readout on the spatial axes reads one axis's share.** -/
theorem normalized_share (share : Fin 4 → ℝ) (Yn : ℝ) (hexact : share 0 = 0)
    (h12 : share 1 = share 2) (h13 : share 1 = share 3) (hsum : ∑ i, share i = Yn)
    (w : Fin 4 → ℝ) (hw0 : w 0 = 0) (hw : ∑ i, w i = 1) :
    ∑ i, w i * share i = Yn / 3 := by
  have hs := NoiseShare.share_spatial share Yn hexact h12 h13 hsum
  rw [Fin.sum_univ_four] at hw ⊢
  rw [hexact, hs 1 (by decide), hs 2 (by decide), hs 3 (by decide), hw0]
  have : w 1 + w 2 + w 3 = 1 := by linarith
  linear_combination (Yn / 3) * this

/-- A law with weight `w₀` on the time axis reads `(1 − w₀) Y/3`. -/
theorem time_weight (share : Fin 4 → ℝ) (Yn : ℝ) (hexact : share 0 = 0)
    (h12 : share 1 = share 2) (h13 : share 1 = share 3) (hsum : ∑ i, share i = Yn)
    (w : Fin 4 → ℝ) (hw : ∑ i, w i = 1) :
    ∑ i, w i * share i = (1 - w 0) * (Yn / 3) := by
  have hs := NoiseShare.share_spatial share Yn hexact h12 h13 hsum
  rw [Fin.sum_univ_four] at hw ⊢
  rw [hexact, hs 1 (by decide), hs 2 (by decide), hs 3 (by decide)]
  have : w 1 + w 2 + w 3 = 1 - w 0 := by linarith
  linear_combination (Yn / 3) * this

theorem uniform_four (share : Fin 4 → ℝ) (Yn : ℝ) (hexact : share 0 = 0)
    (h12 : share 1 = share 2) (h13 : share 1 = share 3) (hsum : ∑ i, share i = Yn) :
    ∑ i, (1/4 : ℝ) * share i = Yn / 4 := by
  rw [time_weight share Yn hexact h12 h13 hsum (fun _ => 1/4) (by norm_num [Fin.sum_univ_four])]; ring

end PMConstants.VevReadout
