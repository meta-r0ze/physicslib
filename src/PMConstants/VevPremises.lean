import PMConstants.VevAccounting
import PMConstants.EventStiffness

/-!
# Calibration of the VEV handoff

Under the event calibration `toll·m = 1/(4πα N_sys)`, the handoff reads
`α⁻¹ = 4π · N_sys · (toll·m)`. Each interface slot costs one repair of the
footprint over the full solid angle in units of the electron's one repair
(`RootRepairRule.electron_one_event`). The wire-share comparison is in
`E8PConstants.VevWindow`.
-/

noncomputable section
namespace PMConstants.VevPremises
open PMConstants ElectroweakE8 CertifiedConstants ElectroweakBounds VevAccounting

theorem handoff_is_footprint_repair {toll : ℝ} {m : ℕ} (hα : 0 < α)
    (hcal : toll * m = 1 / (4 * Real.pi * α * footprint)) :
    1 / α = 4 * Real.pi * footprint * (toll * m) := by
  have hf : (0 : ℝ) < footprint := by norm_num [footprint, overhead]
  rw [hcal]; field_simp

end PMConstants.VevPremises
