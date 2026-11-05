import PMConstants.CertifiedConstants

/-!
# Joint checks on the proposed electroweak constants

The VEV and electron Yukawa are separate proposed formulas. Their consequences
must also obey the electron mass closure equation if both are to be exact with
the same scalar normalization. We certify their joint residual. No correction
coefficient is fitted and no measured quantity is inferred from this arithmetic.
-/
noncomputable section
namespace PMConstants.JointConstants
open ElectroweakE8 CertifiedConstants

theorem product_bounds {x y a b c d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hx : a < x ∧ x < b) (hy : c < y ∧ y < d) :
    a*c < x*y ∧ x*y < b*d := by
  have hxp : 0 < x := ha.trans hx.1
  have hyp : 0 < y := hc.trans hy.1
  have hbp : 0 < b := hxp.trans hx.2
  constructor
  · exact (mul_lt_mul_of_pos_right hx.1 hc).trans (mul_lt_mul_of_pos_left hy.1 hxp)
  · exact (mul_lt_mul_of_pos_right hx.2 hyp).trans (mul_lt_mul_of_pos_left hy.2 hbp)

theorem inverse_effective_dimension :
    1/effectiveDimension = 2*Real.pi/(8*Real.pi+1) := by
  have hp := Real.pi_pos
  have hd := effective_dimension_pos
  unfold effectiveDimension at *
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.chi_eq] at *
  field_simp
  ring

theorem inverse_dimension_bounds :
    (0.2404334567 : ℝ) < 1/effectiveDimension ∧
      1/effectiveDimension < 0.2404334568 := by
  rw [inverse_effective_dimension]
  have hd : 0 < 8*Real.pi+1 := by positivity
  constructor
  · apply (lt_div_iff₀ hd).mpr
    nlinarith [Real.pi_gt_d20]
  · apply (div_lt_iff₀ hd).mpr
    nlinarith [Real.pi_lt_d20]

theorem vev_reduced {a : ℝ} (ha : a ≠ 0) :
    vevRatio a = 3510 * (1/a + 1/effectiveDimension) *
      (1 - bareYukawa / ((PMSubstrate.E8Values.sigma : ℝ) - (PMSubstrate.E8Values.chi : ℝ))) := by
  have hd := effective_dimension_pos.ne'
  unfold vevRatio
  rw [show ((PMSubstrate.E8Values.chi : ℝ) * (PMSubstrate.E8Values.Delta : ℝ)^2 -
      ((PMSubstrate.E8Values.nu : ℝ) + (PMSubstrate.E8Values.D : ℝ) *
        (PMSubstrate.E8Values.Delta : ℝ))) = 3510 by
    rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.Delta_eq,
      PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.D_eq]
    norm_num]
  apply congrArg (fun z : ℝ => z * (1 - bareYukawa /
    ((PMSubstrate.E8Values.sigma : ℝ) - (PMSubstrate.E8Values.chi : ℝ))))
  field_simp [ha, hd]
 

theorem vev_ratio_bounds :
    (481839.81165 : ℝ) < vevRatio α ∧ vevRatio α < 481839.81166 := by
  have ha := PMSubstrate.causalCoupling_bounds.1
  have hz := PMSubstrate.geometricIndex_bounds
  have hd := inverse_dimension_bounds
  have hi : 1/α = PMSubstrate.geometricIndex := by simp [α, PMSubstrate.causalCoupling]
  rw [vev_reduced ha.ne', hi]
  norm_num [one_div] at hd
  norm_num [bareYukawa]
  constructor <;> nlinarith [hz.1, hz.2, hd.1, hd.2]

theorem sqrt_two_bounds :
    (1.4142135623 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.4142135624 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

theorem electron_vev_product_bounds :
    (1.41382730 : ℝ) < electronYukawa α * vevRatio α ∧
      electronYukawa α * vevRatio α < 1.41382732 := by
  have h := product_bounds (by norm_num) (by norm_num)
    electron_yukawa_bounds vev_ratio_bounds
  constructor <;> nlinarith [h.1, h.2]

/-- The electron mass predicted by the two stipulated formulas, divided by
the same electron input used to normalize the VEV. -/
def electronClosureRatio : ℝ := electronYukawa α * vevRatio α / Real.sqrt 2

theorem electron_closure_bounds :
    (0.99972687 : ℝ) < electronClosureRatio ∧ electronClosureRatio < 0.99972689 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hb := sqrt_two_bounds
  have hp := electron_vev_product_bounds
  unfold electronClosureRatio
  constructor
  · apply (lt_div_iff₀ hs).mpr
    nlinarith [hb.1, hb.2, hp.1, hp.2]
  · apply (div_lt_iff₀ hs).mpr
    nlinarith [hb.1, hb.2, hp.1, hp.2]

theorem electron_deficit_bounds :
    (0.00027311 : ℝ) < 1-electronClosureRatio ∧
      1-electronClosureRatio < 0.00027313 := by
  constructor <;> linarith [electron_closure_bounds.1, electron_closure_bounds.2]

/-- The formulas cannot both close the exact electron mass law merely by
changing the overall mass unit. Higher-order/response corrections need deriving. -/
theorem no_exact_electron_closure {me : ℝ} (hme : me ≠ 0) :
    electronYukawa α * vev α me / Real.sqrt 2 ≠ me := by
  intro he
  have h := (electron_mass_closure hme).mp he
  have hr : electronClosureRatio = 1 := by
    unfold electronClosureRatio
    rw [h]; exact div_self (by positivity)
  have := electron_closure_bounds.2
  rw [hr] at this
  norm_num at this

end PMConstants.JointConstants
