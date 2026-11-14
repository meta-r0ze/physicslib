import PMFlavor.CKM

/-!
# The reactor angle as a node conductance into the spatial axes

The PMNS reactor angle is written `sin²θ₁₃ = (σ − χ)/α⁻¹`. Its pieces are E8 quantities with
established readings:
* `α = 1/Z_geo` is the node admittance in units of one open channel (`PMSubstrate.causalCoupling`),
  and a node's through weight is its conductance in those units
  (`PMConstants.HandoffAdmittance.node_current`, Landauer's relation derived from the two streams);
* `σ − χ = D − 1` are the spatial axes (`PMConstants.VevLedger.noiseDenominator_eq_orthogonal`),
  the axes on which readout events occur (`PMConstants.VevEvent`).

**Construction.** A transfer through the node into any of the `D − 1` spatial-axis channels in
parallel (admittances add, `PMSubstrate.ProtocolToll`) has probability `(D − 1)/Z_geo`.

**Tests (NuFIT `0.02225 ± 0.00056`).**
* `channel_count_unique`: among `n/Z_geo` for every natural `n`, only `n = 3` lies within `3σ`;
  every other count is more than `12σ` away.
* `series_corrections_unresolved`: a boundary `π` or a closure `χ` in series with the node shifts
  the value by about `2%`, which stays within `2σ`; the data do not resolve corrections of order
  `π/Z_geo`.
* `four_boundaries_excluded`: four boundaries in series (`3/(Z_geo + 4π)`) are excluded.

So the construction fixes the channel count; corrections below the data's resolution stay open.
-/

noncomputable section
namespace PMFlavor.ReactorConductance
open PMFlavor.CKM

lemma αinv_pos : 0 < αinv := by linarith [ai_bounds.1]

/-- **Only three channels fit.** -/
theorem channel_count_unique (n : ℕ) :
    |((n : ℝ) / αinv - 0.02225) / 0.00056| < 3 ↔ n = 3 := by
  have ha := ai_bounds
  have hpos := αinv_pos
  constructor
  · intro h
    rw [abs_lt] at h
    obtain ⟨h1, h2⟩ := h
    rw [lt_div_iff₀ (by norm_num)] at h1
    rw [div_lt_iff₀ (by norm_num)] at h2
    have e1 : (n : ℝ) < (0.02225 + 3 * 0.00056) * αinv :=
      (div_lt_iff₀ hpos).1 (by linarith)
    have e2 : (0.02225 - 3 * 0.00056) * αinv < n :=
      (lt_div_iff₀ hpos).1 (by linarith)
    have u : (n : ℝ) < 4 := by nlinarith
    have l : (2 : ℝ) < n := by nlinarith
    have u' : n < 4 := by exact_mod_cast u
    have l' : 2 < n := by exact_mod_cast l
    omega
  · rintro rfl
    have q1 : (3 : ℝ) / αinv < 0.0218921 := by rw [div_lt_iff₀ hpos]; nlinarith
    have q2 : 0.0218920 < (3 : ℝ) / αinv := by rw [lt_div_iff₀ hpos]; nlinarith
    push_cast
    rw [abs_lt]; constructor
    · rw [lt_div_iff₀ (by norm_num)]; linarith
    · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- **Series corrections of order `π/Z_geo` are below the data's resolution.** -/
theorem series_corrections_unresolved :
    |(3 / (αinv + Real.pi) - 0.02225) / 0.00056| < 2 ∧
      |(3 / (αinv + 2) - 0.02225) / 0.00056| < 2 := by
  have ha := ai_bounds
  have hp := Real.pi_gt_d2
  have hp' := Real.pi_lt_d2
  have d1 : 0 < αinv + Real.pi := by linarith
  have d2 : 0 < αinv + 2 := by linarith
  have a1 : 3 / (αinv + Real.pi) < 0.02141 := by rw [div_lt_iff₀ d1]; nlinarith
  have a2 : 0.02139 < 3 / (αinv + Real.pi) := by rw [lt_div_iff₀ d1]; nlinarith
  have b1 : 3 / (αinv + 2) < 0.02158 := by rw [div_lt_iff₀ d2]; nlinarith
  have b2 : 0.02157 < 3 / (αinv + 2) := by rw [lt_div_iff₀ d2]; nlinarith
  constructor <;> rw [abs_lt] <;> constructor <;>
    first
    | (rw [lt_div_iff₀ (by norm_num)]; linarith)
    | (rw [div_lt_iff₀ (by norm_num)]; linarith)

/-- **Four boundaries in series are excluded.** -/
theorem four_boundaries_excluded : 3 < |(3 / (αinv + 4 * Real.pi) - 0.02225) / 0.00056| := by
  have ha := ai_bounds
  have hp := Real.pi_gt_d2
  have d : 0 < αinv + 4 * Real.pi := by linarith
  have a : 3 / (αinv + 4 * Real.pi) < 0.02006 := by rw [div_lt_iff₀ d]; nlinarith
  have x : (3 / (αinv + 4 * Real.pi) - 0.02225) / 0.00056 < -3 := by
    rw [div_lt_iff₀ (by norm_num)]; linarith
  exact lt_abs.2 (Or.inr (by linarith))

end PMFlavor.ReactorConductance
