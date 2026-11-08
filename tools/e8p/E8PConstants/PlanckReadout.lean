import PMConstants.GravityAccounting
import PMConstants.Depth

/-!
# Planck mass from the certified gravitational coupling (comparison readout)

`m_P = m_e/√α_G`. The electron mass is the supplied CODATA input — a comparison
value, so this readout lives with the e8p comparison tool rather than in the
axiom-checked derivation tree. The only E8 content is the enclosure of `α_G` in
`GravityAccounting.channels_as_frame`.
-/

noncomputable section
namespace E8PConstants.PlanckReadout

open PMConstants
open PMConstants.CertifiedConstants

/-- Electron mass in GeV (CODATA 2022), a supplied comparison input. -/
def electronMassGeV : ℝ := 0.00051099895069

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
  unfold planckMass PMConstants.Depth.planck electronMassGeV
  constructor
  · rw [lt_div_iff₀ hpos]
    nlinarith [hs2]
  · rw [div_lt_iff₀ hpos]
    nlinarith [hs1]

end E8PConstants.PlanckReadout
