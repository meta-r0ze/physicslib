import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ZetaValues

/-!
# The logarithmic integral for the one-loop radiative calculation

On `[0, 1]` the real dilogarithm series agrees with the integral of
`−log(1 − x)/x`. The logarithm series gives the kernel on the open
interval. The integrated monomials are dominated by the Basel series,
which justifies integrating the series through the endpoint.
-/

noncomputable section
namespace PMElementaryParticles.RadiativeIntegrals

open MeasureTheory Set
open scoped Interval

/-- The real dilogarithm series, used on the unit interval. -/
def dilog (z : ℝ) : ℝ := ∑' n : ℕ, z ^ (n + 1) / (n + 1 : ℝ) ^ 2

private def term (n : ℕ) (x : ℝ) : ℝ := x ^ n / (n + 1 : ℝ)

private theorem term_hasSum {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n => term n x) (-Real.log (1 - x) / x) := by
  have habs : |x| < 1 := by rw [abs_of_pos hx.1]; exact hx.2
  convert (Real.hasSum_pow_div_log_of_abs_lt_one habs).div_const x using 1
  funext n
  simp only [term, pow_succ]
  field_simp [hx.1.ne']

private theorem term_integral {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    (∫ x in Ioo (0 : ℝ) z, term n x) = z ^ (n + 1) / (n + 1 : ℝ) ^ 2 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hz]
  simp [term, integral_pow, div_div, pow_two]

private theorem basel_succ :
    HasSum (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using h

/-- The series is the logarithmic kernel's interval integral, including at one. -/
theorem dilog_eq_integral {z : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z ≤ 1) :
    dilog z = ∫ x in (0 : ℝ)..z, -Real.log (1 - x) / x := by
  let μ := volume.restrict (Ioo (0 : ℝ) z)
  have hmem : ∀ᵐ x ∂μ, x ∈ Ioo (0 : ℝ) z := ae_restrict_mem measurableSet_Ioo
  have hi (n : ℕ) : Integrable (term n) μ := by
    have hc : Continuous (term n) := by unfold term; fun_prop
    exact hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hnorm (n : ℕ) : (∫ x, ‖term n x‖ ∂μ) = ∫ x, term n x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hmem] with x hx
    exact Real.norm_of_nonneg (div_nonneg (pow_nonneg hx.1.le _) (by positivity))
  have hs : Summable (fun n => ∫ x, ‖term n x‖ ∂μ) := by
    simp_rw [hnorm]
    dsimp only [μ]
    simp_rw [term_integral hz₀]
    refine basel_succ.summable.of_nonneg_of_le (fun n => by positivity) fun n => ?_
    exact div_le_div_of_nonneg_right (pow_le_one₀ hz₀ hz₁) (by positivity)
  have hk : ∀ᵐ x ∂μ, (∑' n, term n x) = -Real.log (1 - x) / x := by
    filter_upwards [hmem] with x hx
    exact (term_hasSum ⟨hx.1, hx.2.trans_le hz₁⟩).tsum_eq
  calc
    dilog z = ∑' n, ∫ x, term n x ∂μ := by
      unfold dilog
      dsimp only [μ]
      simp_rw [term_integral hz₀]
    _ = ∫ x, (∑' n, term n x) ∂μ := integral_tsum_of_summable_integral_norm hi hs
    _ = ∫ x, -Real.log (1 - x) / x ∂μ := integral_congr_ae hk
    _ = ∫ x in (0 : ℝ)..z, -Real.log (1 - x) / x := by
      rw [intervalIntegral.integral_of_le hz₀, integral_Ioc_eq_integral_Ioo]

theorem dilog_one : dilog 1 = Real.pi ^ 2 / 6 := by
  simpa [dilog] using basel_succ.tsum_eq

theorem integral_neg_log_one_sub_div :
    (∫ x in (0 : ℝ)..1, -Real.log (1 - x) / x) = Real.pi ^ 2 / 6 := by
  rw [← dilog_eq_integral zero_le_one le_rfl, dilog_one]

theorem intervalIntegrable_neg_log_one_sub_div :
    IntervalIntegrable (fun x : ℝ => -Real.log (1 - x) / x) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one, IntegrableOn]
  apply Integrable.of_integral_ne_zero
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_neg_log_one_sub_div]
  positivity

/-- The reflected form, under the substitution `x ↦ 1 − x`. -/
theorem integral_neg_log_div_one_sub :
    (∫ x in (0 : ℝ)..1, -Real.log x / (1 - x)) = Real.pi ^ 2 / 6 := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
    (fun x => -Real.log (1 - x) / x) 1
  simpa only [sub_sub_cancel, sub_self, sub_zero, integral_neg_log_one_sub_div] using h

end PMElementaryParticles.RadiativeIntegrals
