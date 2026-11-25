import PMConstants.ElectroweakBounds
import PMConstants.ContentWeight

/-! The VEV as a function of the subtracted frame footprint. -/

noncomputable section
namespace PMConstants.VevAccounting
open PMConstants ElectroweakE8 CertifiedConstants ElectroweakBounds

/-- The formula with a general subtraction `L`. -/
def vevWith (L : ℝ) : ℝ := vev α electronGeV * ((2 * 43^2 - L) / 3510)

theorem frame_is_paper : vevWith 188 = vev α electronGeV := by
  unfold vevWith; norm_num

end PMConstants.VevAccounting
