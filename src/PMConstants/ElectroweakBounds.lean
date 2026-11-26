import PMConstants.JointConstants
import PMConstants.GaugeSpectrum
import PMSubstrate.SIUnits

/-! Certified consequences of the proposed formulas. `electronGeV` is the
mass unit (CODATA 2022, `PMSubstrate.SIUnits`), not an E8-derived number.
Gauge masses here use the displayed quadratic response at the same coupling
and VEV; running/response corrections are not silently supplied.
-/
noncomputable section
namespace PMConstants.ElectroweakBounds
open ElectroweakE8 CertifiedConstants JointConstants GaugeSpectrum

def electronGeV : ℝ := PMSubstrate.SIUnits.electronMassGeV

theorem vev_bounds : (246.2196381 : ℝ) < vev PMSubstrate.causalCoupling electronGeV ∧
    vev PMSubstrate.causalCoupling electronGeV < 246.2196382 := by
  have h := vev_ratio_bounds
  unfold vev electronGeV PMSubstrate.SIUnits.electronMassGeV
  constructor <;> nlinarith [h.1, h.2]

theorem scalar_root_bounds :
    (0.5087704005 : ℝ) < Real.sqrt (2*selfCoupling) ∧
      Real.sqrt (2*selfCoupling) < 0.5087704007 := by
  have hs : (Real.sqrt (2*selfCoupling))^2 = (256 : ℝ)/989 := by
    rw [Real.sq_sqrt (show 0 ≤ 2*selfCoupling by linarith [self_coupling_pos])]
    norm_num [selfCoupling]
  have hn := Real.sqrt_nonneg (2*selfCoupling)
  constructor <;> nlinarith

theorem higgs_bounds : (125.2692638 : ℝ) < higgsMass PMSubstrate.causalCoupling electronGeV ∧
    higgsMass PMSubstrate.causalCoupling electronGeV < 125.2692640 := by
  have h := product_bounds (by norm_num) (by norm_num) scalar_root_bounds vev_bounds
  unfold higgsMass
  constructor <;> nlinarith [h.1, h.2]

theorem vev_squared_bounds :
    (246.2196381 : ℝ)^2 < (vev PMSubstrate.causalCoupling electronGeV)^2 ∧
      (vev PMSubstrate.causalCoupling electronGeV)^2 < (246.2196382 : ℝ)^2 := by
  have h := vev_bounds
  constructor <;> nlinarith [h.1, h.2]

theorem fermi_bounds :
    (0.00001166378 : ℝ) < fermi PMSubstrate.causalCoupling electronGeV ∧ fermi PMSubstrate.causalCoupling electronGeV < 0.00001166380 := by
  have h := product_bounds (by norm_num) (by norm_num) sqrt_two_bounds vev_squared_bounds
  have hd : 0 < Real.sqrt 2 * (vev PMSubstrate.causalCoupling electronGeV)^2 := by nlinarith [h.1]
  unfold fermi
  constructor
  · apply (lt_div_iff₀ hd).mpr; nlinarith [h.1, h.2]
  · apply (div_lt_iff₀ hd).mpr; nlinarith [h.1, h.2]

theorem pi_bounds : (3.1415926535 : ℝ) < Real.pi ∧ Real.pi < 3.1415926536 := by
  constructor <;> nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

theorem weak_squared_bounds :
    (0.4113908 : ℝ) < weakSquared PMSubstrate.causalCoupling ∧ weakSquared PMSubstrate.causalCoupling < 0.4113910 := by
  have h := product_bounds (by norm_num) (by norm_num) pi_bounds alpha_bounds
  unfold weakSquared
  norm_num [clockRatio, footprint, overhead]
  constructor <;> nlinarith [h.1, h.2]

theorem hypercharge_squared_bounds :
    (0.1180052 : ℝ) < hyperchargeSquared PMSubstrate.causalCoupling ∧ hyperchargeSquared PMSubstrate.causalCoupling < 0.1180053 := by
  have h := product_bounds (by norm_num) (by norm_num) pi_bounds alpha_bounds
  unfold hyperchargeSquared
  norm_num [clockRatio, footprint, overhead]
  constructor <;> nlinarith [h.1, h.2]

theorem strong_squared_bounds :
    (1.4816 : ℝ) < strongSquared PMSubstrate.causalCoupling ∧ strongSquared PMSubstrate.causalCoupling < 1.4817 := by
  have h := product_bounds (by norm_num) (by norm_num) pi_bounds strong_bounds
  unfold strongSquared
  constructor <;> nlinarith [h.1, h.2]

theorem w_squared_bounds :
    (78.96 : ℝ)^2 < wMassSquared PMSubstrate.causalCoupling electronGeV ∧ wMassSquared PMSubstrate.causalCoupling electronGeV < (78.97 : ℝ)^2 := by
  have h := product_bounds (by norm_num) (by norm_num) weak_squared_bounds vev_squared_bounds
  unfold wMassSquared
  constructor <;> nlinarith [h.1, h.2]

theorem z_squared_bounds :
    (89.57 : ℝ)^2 < zMassSquared PMSubstrate.causalCoupling electronGeV ∧ zMassSquared PMSubstrate.causalCoupling electronGeV < (89.58 : ℝ)^2 := by
  have hc : (0.5293960 : ℝ) < weakSquared PMSubstrate.causalCoupling+hyperchargeSquared PMSubstrate.causalCoupling ∧
      weakSquared PMSubstrate.causalCoupling+hyperchargeSquared PMSubstrate.causalCoupling < 0.5293963 := by
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
    (78.96 : ℝ) < Real.sqrt (wMassSquared PMSubstrate.causalCoupling electronGeV) ∧
      Real.sqrt (wMassSquared PMSubstrate.causalCoupling electronGeV) < 78.97 :=
  positive_root_bounds (by norm_num) (by norm_num) w_squared_bounds

theorem coupling_bounds :
    ((0.6413 : ℝ) < Real.sqrt (weakSquared PMSubstrate.causalCoupling) ∧ Real.sqrt (weakSquared PMSubstrate.causalCoupling) < 0.6415) ∧
    ((0.3435 : ℝ) < Real.sqrt (hyperchargeSquared PMSubstrate.causalCoupling) ∧ Real.sqrt (hyperchargeSquared PMSubstrate.causalCoupling) < 0.3436) ∧
    ((1.2172 : ℝ) < Real.sqrt (strongSquared PMSubstrate.causalCoupling) ∧ Real.sqrt (strongSquared PMSubstrate.causalCoupling) < 1.2173) := by
  refine ⟨positive_root_bounds (by norm_num) (by norm_num) ?_,
    positive_root_bounds (by norm_num) (by norm_num) ?_,
    positive_root_bounds (by norm_num) (by norm_num) ?_⟩
  · constructor <;> nlinarith [weak_squared_bounds.1, weak_squared_bounds.2]
  · constructor <;> nlinarith [hypercharge_squared_bounds.1, hypercharge_squared_bounds.2]
  · constructor <;> nlinarith [strong_squared_bounds.1, strong_squared_bounds.2]

theorem z_mass_bounds :
    (89.57 : ℝ) < Real.sqrt (zMassSquared PMSubstrate.causalCoupling electronGeV) ∧
      Real.sqrt (zMassSquared PMSubstrate.causalCoupling electronGeV) < 89.58 :=
  positive_root_bounds (by norm_num) (by norm_num) z_squared_bounds

end PMConstants.ElectroweakBounds
