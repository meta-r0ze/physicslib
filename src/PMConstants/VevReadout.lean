import PMConstants.NoiseShare
import PMConstants.RepairBudget

/-!
# The VEV corrections as one exact repair, read out once

`VevCorrections` pinned the VEV's two correction factors with the Fermi window, `(1 + x)` with
`x = α/D_eff` and `(1 − Y/3)`, and left two persistence readings as premises: the linear form is
"one repair", and the noise divisor is the share of one axis. This module derives both from what is
now proved about exact repair and normalized readout, and shows the data exclude the alternatives
each reading rules out.

**The linear form.**
* `exact_net_is_identity`: a repair that returns every displacement exactly has net correction
  equal to the displacement, `d ↦ d`, linear with no higher-order terms. One exact repair of a
  relative displacement `x` gives the factor `1 + x`.
* `residual_series`: if each repair left a residual fraction `r` that was repaired again, the
  factor would be `1 + x/(1 − r)`. Exactness is `r = 0`, giving `1 + x`; `r = x` gives `1/(1 − x)`,
  the geometric form (`VevCorrections.geometric_excluded`).
* `compound_lower`, `compound_excluded`: replacing the one repair by `n ≥ 2` equal partial repairs
  gives `(1 + x/n)ⁿ ≥ 1 + x + x²/4`, which the Fermi window excludes for every `n ≥ 2`; `n → ∞` is
  `eˣ` (`VevCorrections.exp_excluded`). Only `n = 1`, which is `PersistenceClosures.one_repair`, fits.

**One axis's share.**
* `normalized_share`: with the noise shares fixed by exact repair (`NoiseShare.share_spatial`:
  `0` on the reference's time axis, `Y/3` on each spatial axis), *any* normalized readout law on the
  spatial axes reads `Y/3`. The readout does not have to pick one axis; equal shares make every
  normalized spatial law read one axis's share.
* `time_weight`: a normalized law putting weight `w₀` on the time axis reads `(1 − w₀) Y/3`; the
  uniform law over all four axes reads `Y/4` (`uniform_four`). Both `3` and `4` fit the window, so
  this is the one place the premise matters: the VEV readout is a link comparison, and link hops are
  spatial.
* `total_excluded`: an unnormalized total over the three axes reads `Y` (divisor `1`), which the
  window excludes.

Premises: the topological factor is one exact repair of the relative displacement `x`; the VEV is a
normalized readout taken along link (spatial) hops.
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

/-- **Partial repairs are excluded by the Fermi window.** -/
theorem compound_excluded (n : ℕ) (hn : 2 ≤ n) : 246.21971 < V * (1 + x / n) ^ n / (1 + x) := by
  have hv := V_bounds
  have hx := x_bounds
  have hc := compound_lower x (by linarith) n hn
  have hpos : 0 < 1 + x := by linarith
  rw [lt_div_iff₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_left hc (by linarith : (0:ℝ) ≤ V)]

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

/-- **An unnormalized total reads `Y`: divisor `1`, excluded.** -/
theorem total_excluded : ¬ (246.21957 < withDivisor (1 : ℕ) ∧ withDivisor (1 : ℕ) < 246.21971) := by
  rw [divisor_window 1 (by norm_num)]; omega

/-- **The VEV with both readings.** -/
theorem vev_from_readout :
    246.21957 < withDivisor (3 : ℕ) ∧ withDivisor (3 : ℕ) < 246.21971 :=
  (divisor_window 3 (by norm_num)).mpr (Or.inl rfl)

end PMConstants.VevReadout
