import PMConstants.Values

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
  (`PMConstants.VevAccounting.fermi_window`).
* `geometric_excluded`: `1/(1 − x)`, the sum `Σ xᵏ`, puts `v` above `246.22038` GeV.
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

end E8PConstants.VevFormPulls
