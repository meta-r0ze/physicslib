import PMConstants.VevAccounting
import PMConstants.PersistenceClosures
import PMConstants.RequirementRows

/-! VEV correction forms and certified substrate enclosures. -/

noncomputable section
namespace PMConstants.VevCorrections
open PMConstants ElectroweakE8 CertifiedConstants ElectroweakBounds

def V : ℝ := vev PMSubstrate.causalCoupling electronGeV
def Y : ℝ := bareYukawa
def x : ℝ := PMSubstrate.causalCoupling / effectiveDimension

lemma V_bounds : (246.2196381 : ℝ) < V ∧ V < 246.2196382 := vev_bounds

lemma Y_val : Y = 1 / (31 * 6 * 43 ^ 2) := by
  unfold Y bareYukawa
  rw [PMSubstrate.E8Values.embeddingLoad_eq, PMSubstrate.E8Values.D_eq,
    PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.Delta_eq]
  norm_num

lemma x_bounds : (0.0017545277 : ℝ) < x ∧ x < 0.0017545279 := by
  have ha := alpha_bounds
  have hd := JointConstants.inverse_dimension_bounds
  have : x = PMSubstrate.causalCoupling * (1 / effectiveDimension) := by unfold x; ring
  rw [this]; constructor <;> nlinarith [ha.1, ha.2, hd.1, hd.2]

/-- The formula with noise divisor `k`. -/
def withDivisor (k : ℝ) : ℝ := V * (1 - Y / k) / (1 - Y / 3)

/-- The formula with effective dimension `Dp` in place of `D_eff`. -/
def withDimension (Dp : ℝ) : ℝ := V * (1 + PMSubstrate.causalCoupling / Dp) / (1 + x)

end PMConstants.VevCorrections
