import E8PConstants.PMConstants.VevWindow

/-!
# VEV correction-form measured comparisons (moved from the PMConstants leaf)

The VEV's topological factor is `1 + x` with `x = α/D_eff`. The substrate reason for the linear
form is in the library: the anchor's maintenance is one exact repair
(`PMConstants.PersistenceClosures.one_repair`, the electron being a colour and weak singlet by
`RootRepairRule.electron_one_event`), an exact repair's net correction is the displacement itself
(`PMConstants.VevReadout.exact_net_is_identity`), and a re-repaired residual fraction `r` would
give `1 + x/(1 − r)` (`PMConstants.VevReadout.residual_series`): `r = 0` is the linear form,
`r = x` the geometric one, and `n → ∞` equal partial repairs the exponential. Series addition is
exactly first order (`PMConstants.VevImpedance`).

The Fermi window agrees, and that agreement is a comparison, so it lives here.

* `exp_excluded`: `exp x` in place of `1 + x` puts `v` above `246.22001` GeV, outside the window
  `(246.21957, 246.21971)` that the measured Fermi constant fixes
  (`E8PConstants.VevWindow.fermi_window`).
* `geometric_excluded`: `1/(1 − x)`, the sum `Σ xᵏ`, puts `v` above `246.22038` GeV.

Three further exclusions that no library result rests on, moved here for the same reason:

* `noise_needed`: dropping the noise factor `1 − Y/3` puts `v` above `246.21987` GeV.
* `bare_dimension_excluded`: `α/D` without the boundary term puts `v` above `246.2366` GeV. The
  boundary term itself is built in `PMConstants.VevBoundary`.
* `qed_like_excluded`: a QED-like `3α/(4π)` puts `v` below `246.2167` GeV.

The remaining measured-window checks are in `E8PConstants.VevWindow`.
-/

noncomputable section
namespace E8PConstants.VevFormPulls

open PMConstants.Values

/-- Continuous compounding is outside the Fermi window. -/
theorem exp_excluded : 246.22001 < V * Real.exp x / (1 + x) := by
  have hv := V_bounds
  have hx := x_bounds
  have he : 1 + x + x ^ 2 / 2 ≤ Real.exp x := Real.quadratic_le_exp_of_nonneg (by linarith)
  rw [lt_div_iff₀ (by linarith)]
  have : V * (1 + x + x ^ 2 / 2) ≤ V * Real.exp x := mul_le_mul_of_nonneg_left he (by linarith)
  nlinarith

/-- Repairs of repairs are outside the Fermi window. -/
theorem geometric_excluded : 246.22038 < V / ((1 - x) * (1 + x)) := by
  have hv := V_bounds
  have hx := x_bounds
  rw [lt_div_iff₀ (by nlinarith)]
  nlinarith

/-- Dropping the noise factor leaves the window. -/
theorem noise_needed : 246.21987 < V / (1 - Y / 3) := by
  have hv := V_bounds
  rw [lt_div_iff₀ (by norm_num [Y_val])]
  norm_num [Y_val]; nlinarith [hv.1]

/-- The bare dimension, with no boundary term, leaves the window. -/
theorem bare_dimension_excluded : 246.2366 < V * (1 + alpha / 4) / (1 + x) := by
  have hv := V_bounds
  have hx := x_bounds
  have ha := alpha_bounds
  rw [lt_div_iff₀ (by linarith)]
  nlinarith

/-- A QED-like correction leaves the window on the other side. -/
theorem qed_like_excluded : V * (1 + 3 * alpha / (4 * Real.pi)) / (1 + x) < 246.2167 := by
  have hv := V_bounds
  have hx := x_bounds
  have ha := alpha_bounds
  have hp := pi_bounds
  have hq : 3 * alpha / (4 * Real.pi) < 0.0017422 := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  rw [div_lt_iff₀ (by linarith)]
  have h1 : V * (3 * alpha / (4 * Real.pi)) < V * 0.0017422 := mul_lt_mul_of_pos_left hq (by linarith)
  nlinarith

end E8PConstants.VevFormPulls
