import PMConstants.VevDownstream
import PMConstants.ScalarNormalization

/-! **Scalar VEV / substrate-amplitude link.**

Once the scalar normalization is calibrated, the canonical VEV is

```
v = √Z_φ · v_sub.
```

The substrate amplitude is therefore not an independent input: it is the VEV
divided by `√Z_φ`.  This turns the remaining `v_sub` identification into a
definition and leaves only the VEV ledger's named inputs.
-/

noncomputable section
namespace PMConstants.ScalarVevLink

open PMConstants ElectroweakE8 ScalarNormalization ChainCouplings

/-- Calibrated scalar wavefunction normalization. -/
def zPhiCalibrated (α : ℝ) : ℝ :=
  3 / (8 * Real.pi * α * footprint)

/-- Substrate amplitude recovered from the VEV. -/
def vsubOfVev (α me : ℝ) : ℝ :=
  vev α me / Real.sqrt (zPhiCalibrated α)

theorem zPhiCalibrated_pos {α : ℝ} (hα : 0 < α) : 0 < zPhiCalibrated α := by
  have hf : 0 < footprint := by norm_num [footprint, overhead]
  unfold zPhiCalibrated
  positivity

/-- With the scalar calibration, the canonical VEV equals the VEV ledger value. -/
theorem canonicalVev_vsubOfVev {toll : ℝ} {m : ℕ} {α me : ℝ} (hα : 0 < α)
    (hcal : toll * m = 1 / (2 * Real.pi * α * footprint)) :
    canonicalVev toll m (vsubOfVev α me) = vev α me := by
  have hz : zPhi toll m = zPhiCalibrated α := by
    unfold zPhiCalibrated
    exact scalar_z hcal
  have hzpos : 0 < zPhiCalibrated α := zPhiCalibrated_pos hα
  have hs : Real.sqrt (zPhiCalibrated α) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hzpos)
  unfold canonicalVev vsubOfVev
  rw [hz]
  calc
    Real.sqrt (zPhiCalibrated α) * (vev α me / Real.sqrt (zPhiCalibrated α))
        = vev α me * (Real.sqrt (zPhiCalibrated α) / Real.sqrt (zPhiCalibrated α)) := by ring
    _ = vev α me := by rw [div_self hs, mul_one]

/-- W mass in terms of the VEV, with no independent `v_sub` input. -/
theorem w_mass_from_vev {toll : ℝ} {m : ℕ} {α me : ℝ} (hα : 0 < α) (ht : 0 < toll)
    (hm : 0 < m) (hcal : toll * m = 1 / (2 * Real.pi * α * footprint)) :
    chainCoupling (1 / 2) toll m 43 * (vev α me) ^ 2 / 4 =
      3 / 344 * (vsubOfVev α me) ^ 2 := by
  rw [← canonicalVev_vsubOfVev hα hcal]
  exact w_mass_geometric ht hm (vsubOfVev α me)

/-- Z mass in terms of the VEV. -/
theorem z_mass_from_vev {toll : ℝ} {m : ℕ} {α me : ℝ} (hα : 0 < α) (ht : 0 < toll)
    (hm : 0 < m) (hcal : toll * m = 1 / (2 * Real.pi * α * footprint)) :
    (chainCoupling (1 / 2) toll m 43 + chainCoupling (1 / 2) toll m (footprint - 43)) *
        (vev α me) ^ 2 / 4 =
      3 / 8 * (footprint / (43 * (footprint - 43))) * (vsubOfVev α me) ^ 2 := by
  rw [← canonicalVev_vsubOfVev hα hcal]
  exact z_mass_geometric ht hm (vsubOfVev α me)

end PMConstants.ScalarVevLink
