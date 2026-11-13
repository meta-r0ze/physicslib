import PMConstants.GravityAccounting
import PMConstants.Depth
import PMSubstrate.SIUnits

/-!
**Comparison / unit conversion.**

# Planck mass from the certified gravitational coupling

`m_P = m_e/√α_G`. The E8 content is the enclosure of `α_G` in
`GravityAccounting.channels_as_frame`; the electron mass is the CODATA unit input, as in
`PMElementaryParticles.PhysicalUnits`. Reported by `e8p` as `planck_mass`.
-/

noncomputable section
namespace PMConstants.PlanckReadout

open PMConstants
open PMConstants.CertifiedConstants

/-- Electron mass in GeV (CODATA 2022), a supplied comparison input. -/
def electronMassGeV : ℝ := PMSubstrate.SIUnits.electronMassGeV

/-- Planck mass in GeV read out from the certified `α_G`. -/
def planckMass : ℝ := PMConstants.Depth.planck electronMassGeV (PMConstants.Depth.gravity α)

theorem planckMass_bounds :
    (1.22089354e19 : ℝ) < planckMass ∧ planckMass < 1.22089358e19 := by
  have hg := PMConstants.GravityAccounting.channels_as_frame
  have hs1 : (4.1854503939e-23 : ℝ) < Real.sqrt (PMConstants.Depth.gravity α) := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith [hg.1]
  have hs2 : Real.sqrt (PMConstants.Depth.gravity α) < (4.1854505134e-23 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    linarith [hg.2]
  have hpos : 0 < Real.sqrt (PMConstants.Depth.gravity α) := by linarith
  unfold planckMass PMConstants.Depth.planck electronMassGeV PMSubstrate.SIUnits.electronMassGeV
  constructor
  · rw [lt_div_iff₀ hpos]
    nlinarith [hs2]
  · rw [div_lt_iff₀ hpos]
    nlinarith [hs1]

end PMConstants.PlanckReadout
