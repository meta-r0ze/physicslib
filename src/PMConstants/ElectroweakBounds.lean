import PMConstants.JointConstants
import PMConstants.GaugeSpectrum

/-! Certified consequences of the proposed formulas. `electronGeV` is the
existing calculator's experimental mass-unit input, not an E8-derived number.
Gauge masses here use the displayed quadratic response at the same coupling
and VEV; running/response corrections are not silently supplied.
-/
noncomputable section
namespace PMConstants.ElectroweakBounds
open ElectroweakE8 CertifiedConstants JointConstants GaugeSpectrum

def electronGeV : ℝ := 0.00051099895

theorem vev_bounds : (246.2196378 : ℝ) < vev α electronGeV ∧
    vev α electronGeV < 246.2196379 := by
  have h := vev_ratio_bounds
  unfold vev electronGeV
  constructor <;> nlinarith [h.1, h.2]

theorem scalar_root_bounds :
    (0.5087704005 : ℝ) < Real.sqrt (2*selfCoupling) ∧
      Real.sqrt (2*selfCoupling) < 0.5087704007 := by
  have hs : (Real.sqrt (2*selfCoupling))^2 = (256 : ℝ)/989 := by
    rw [Real.sq_sqrt (show 0 ≤ 2*selfCoupling by linarith [self_coupling_pos])]
    norm_num [selfCoupling]
  have hn := Real.sqrt_nonneg (2*selfCoupling)
  constructor <;> nlinarith

theorem higgs_bounds : (125.2692637 : ℝ) < higgsMass α electronGeV ∧
    higgsMass α electronGeV < 125.2692639 := by
  have h := product_bounds (by norm_num) (by norm_num) scalar_root_bounds vev_bounds
  unfold higgsMass
  constructor <;> nlinarith [h.1, h.2]

theorem vev_squared_bounds :
    (246.2196378 : ℝ)^2 < (vev α electronGeV)^2 ∧
      (vev α electronGeV)^2 < (246.2196379 : ℝ)^2 := by
  have h := vev_bounds
  constructor <;> nlinarith [h.1, h.2]

theorem fermi_bounds :
    (0.00001166378 : ℝ) < fermi α electronGeV ∧ fermi α electronGeV < 0.00001166380 := by
  have h := product_bounds (by norm_num) (by norm_num) sqrt_two_bounds vev_squared_bounds
  have hd : 0 < Real.sqrt 2 * (vev α electronGeV)^2 := by nlinarith [h.1]
  unfold fermi
  constructor
  · apply (lt_div_iff₀ hd).mpr; nlinarith [h.1, h.2]
  · apply (div_lt_iff₀ hd).mpr; nlinarith [h.1, h.2]

theorem pi_bounds : (3.1415926535 : ℝ) < Real.pi ∧ Real.pi < 3.1415926536 := by
  constructor <;> nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

theorem weak_squared_bounds :
    (0.4113908 : ℝ) < weakSquared α ∧ weakSquared α < 0.4113910 := by
  have h := product_bounds (by norm_num) (by norm_num) pi_bounds alpha_bounds
  unfold weakSquared
  norm_num [clockRatio, footprint, overhead]
  constructor <;> nlinarith [h.1, h.2]

theorem hypercharge_squared_bounds :
    (0.1180052 : ℝ) < hyperchargeSquared α ∧ hyperchargeSquared α < 0.1180053 := by
  have h := product_bounds (by norm_num) (by norm_num) pi_bounds alpha_bounds
  unfold hyperchargeSquared
  norm_num [clockRatio, footprint, overhead]
  constructor <;> nlinarith [h.1, h.2]

theorem strong_squared_bounds :
    (1.4816 : ℝ) < strongSquared α ∧ strongSquared α < 1.4817 := by
  have h := product_bounds (by norm_num) (by norm_num) pi_bounds strong_bounds
  unfold strongSquared
  constructor <;> nlinarith [h.1, h.2]

theorem w_squared_bounds :
    (78.96 : ℝ)^2 < wMassSquared α electronGeV ∧ wMassSquared α electronGeV < (78.97 : ℝ)^2 := by
  have h := product_bounds (by norm_num) (by norm_num) weak_squared_bounds vev_squared_bounds
  unfold wMassSquared
  constructor <;> nlinarith [h.1, h.2]

theorem z_squared_bounds :
    (89.57 : ℝ)^2 < zMassSquared α electronGeV ∧ zMassSquared α electronGeV < (89.58 : ℝ)^2 := by
  have hc : (0.5293960 : ℝ) < weakSquared α+hyperchargeSquared α ∧
      weakSquared α+hyperchargeSquared α < 0.5293963 := by
    constructor <;> linarith [weak_squared_bounds.1, weak_squared_bounds.2,
      hypercharge_squared_bounds.1, hypercharge_squared_bounds.2]
  have h := product_bounds (by norm_num) (by norm_num) hc vev_squared_bounds
  unfold zMassSquared
  constructor <;> nlinarith [h.1, h.2]

theorem positive_root_bounds {x lo hi : ℝ} (hl : 0 < lo) (hh : 0 < hi)
    (hb : lo^2 < x ∧ x < hi^2) : lo < Real.sqrt x ∧ Real.sqrt x < hi := by
  have hx : 0 ≤ x := by nlinarith [hb.1]
  have hs := Real.sq_sqrt hx
  have hn := Real.sqrt_nonneg x
  constructor <;> nlinarith [hb.1, hb.2]

theorem w_mass_bounds :
    (78.96 : ℝ) < Real.sqrt (wMassSquared α electronGeV) ∧
      Real.sqrt (wMassSquared α electronGeV) < 78.97 :=
  positive_root_bounds (by norm_num) (by norm_num) w_squared_bounds

theorem coupling_bounds :
    ((0.6413 : ℝ) < Real.sqrt (weakSquared α) ∧ Real.sqrt (weakSquared α) < 0.6415) ∧
    ((0.3435 : ℝ) < Real.sqrt (hyperchargeSquared α) ∧ Real.sqrt (hyperchargeSquared α) < 0.3436) ∧
    ((1.2172 : ℝ) < Real.sqrt (strongSquared α) ∧ Real.sqrt (strongSquared α) < 1.2173) := by
  refine ⟨positive_root_bounds (by norm_num) (by norm_num) ?_,
    positive_root_bounds (by norm_num) (by norm_num) ?_,
    positive_root_bounds (by norm_num) (by norm_num) ?_⟩
  · constructor <;> nlinarith [weak_squared_bounds.1, weak_squared_bounds.2]
  · constructor <;> nlinarith [hypercharge_squared_bounds.1, hypercharge_squared_bounds.2]
  · constructor <;> nlinarith [strong_squared_bounds.1, strong_squared_bounds.2]

theorem z_mass_bounds :
    (89.57 : ℝ) < Real.sqrt (zMassSquared α electronGeV) ∧
      Real.sqrt (zMassSquared α electronGeV) < 89.58 :=
  positive_root_bounds (by norm_num) (by norm_num) z_squared_bounds

/-- The measured Z anchor used by the current W calculator is not the Z
mass of the paper's uncorrected quadratic-response formulas. -/
theorem z_anchor_not_derived : Real.sqrt (zMassSquared α electronGeV) ≠ 91.1876 := by
  have h := z_mass_bounds.2
  intro he; rw [he] at h; norm_num at h

end PMConstants.ElectroweakBounds
