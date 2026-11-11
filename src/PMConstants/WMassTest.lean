import PMConstants.Partition

/-!
# The W mass as a parameter-free test of the clock ratio

The paper's weak allocation is the exact rational `s = Δ/N_sys = 1849/8295`. Read as the
on-shell mixing `s = 1 − m_W²/m_Z²`, which `LinkMass` derives from the link cost at tree level
and which is scale-independent by definition, it fixes the ratio of the two masses with no
interface factor `k`, no `α` and no VEV:

* `mass_ratio_sq`: `m_W²/m_Z² = 6446/8295`, and `ratio_bounds`:
  `0.8815297 < m_W/m_Z < 0.8815298`.

This module keeps only the scale-free ratio. The measured `m_Z` window and the
labelled pulls (`w_window`, `pull_world`, `pull_cms`, `pull_cdf`, `pull_sm`) live
in `tools/e8p/E8PConstants/PMConstants/WeakMassPulls.lean`.
-/

noncomputable section
namespace PMConstants.WMassTest
open PMConstants

theorem one_sub_clock : 1 - clockRatio = 6446/8295 := by
  norm_num [clockRatio, footprint, overhead]

def wMass (mZ : ℝ) : ℝ := mZ * Real.sqrt (1 - clockRatio)

theorem on_shell (mZ : ℝ) : wMass mZ ^ 2 = (1 - clockRatio) * mZ ^ 2 := by
  unfold wMass
  rw [mul_pow, Real.sq_sqrt (by rw [one_sub_clock]; norm_num)]; ring

theorem mass_ratio_sq {mZ : ℝ} (h : mZ ≠ 0) : wMass mZ ^ 2 / mZ ^ 2 = 6446/8295 := by
  rw [on_shell, one_sub_clock]; field_simp

theorem ratio_bounds :
    (0.8815297 : ℝ) < Real.sqrt (1 - clockRatio) ∧ Real.sqrt (1 - clockRatio) < 0.8815298 := by
  rw [one_sub_clock]
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

end PMConstants.WMassTest
