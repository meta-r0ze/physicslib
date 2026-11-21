import PMAction.InterWallDiagonal

/-! Measured charged-lepton check for the traceless inter-wall link. -/

noncomputable section
namespace E8PConstants.InterWallDiagonalCheck

open PMAction.InterWallDiagonal

/-- Measured charged-lepton masses in MeV (PDG 2024). -/
def IsMeasuredLepton (m : ℝ) : Prop :=
  m = 0.51099895 ∨ m = 105.6583755 ∨ m = 1776.93

/-- The measured charged leptons are pairwise more than a factor `4` apart. -/
theorem measured_lepton_gaps (a b : ℝ) (ha : IsMeasuredLepton a) (hb : IsMeasuredLepton b) (h : a < b) :
    4 * a < b := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | (norm_num at h; done) | norm_num

/-- The library theorem with the measured gap supplied by `measured_lepton_gaps`. -/
theorem no_measured_lepton_traceless (k a b : ℝ) (hk : 0 < k) (hb : 0 < |b|) (hba : |b| ≤ |a|)
    (hab : |a| ≤ 2 * |b|)
    (hlo : IsMeasuredLepton (k / |a|)) (hhi : IsMeasuredLepton (k / |b|))
    (hne : k / |a| ≠ k / |b|) : False := by
  apply PMAction.InterWallDiagonal.no_measured_lepton_traceless k a b hk hb hba hab
  · exact measured_lepton_gaps _ _ hlo hhi (by
      have hle : k / |a| ≤ k / |b| := div_le_div_of_nonneg_left hk.le hb hba
      exact lt_of_le_of_ne hle hne)
  · exact hne

end E8PConstants.InterWallDiagonalCheck
