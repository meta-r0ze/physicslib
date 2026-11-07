import PMElementaryParticles.LeptonMasses
import PMElementaryParticles.CompositeMasses
import PMElementaryParticles.NeutronRate
import PMFlavor.CKM
import PMConstants.ElectroweakE8
import PMConstants.CurrentConstants
import PMConstants.JointConstants
import PMElementaryParticles.MuonLifetime
import PMSubstrate.E8Values
import Mathlib.Tactic

/-! **Comparison / structural.**

Two-body charged-kaon width:

```
Γ(K⁺ → μ⁺ν) = G_F² f_K² m_K m_μ² (1 − m_μ²/m_K²)² / (8π).
```

`f_K` is a supplied input; the E8 kaon decay constant is still open.
-/

noncomputable section
namespace PMElementaryParticles.KaonWidth

open PMElementaryParticles.LeptonMasses
open PMElementaryParticles.CompositeMasses
open PMElementaryParticles.NeutronRate

def kaonWidth (fK : ℝ) : ℝ :=
  fermiME ^ 2 * fK ^ 2 * kaonPlus * muon ^ 2 *
    (1 - (muon / kaonPlus) ^ 2) ^ 2 / (8 * Real.pi)

def kaonLifetime (fK : ℝ) : ℝ :=
  1 / kaonWidth fK

theorem kaonLifetime_eq (fK : ℝ) : kaonLifetime fK = 1 / kaonWidth fK := rfl

/-- Two-body width with the CKM factor `|Vus|²`. -/
def kaonWidthCKM (fK Vus : ℝ) : ℝ :=
  kaonWidth fK * Vus ^ 2

/-- E8 kaon decay constant `v/(Δ²−ν²) = v/1593`. -/
noncomputable def kaonDecayConstantE8 : ℝ :=
  PMConstants.ElectroweakE8.vev PMConstants.CurrentConstants.alpha 1 /
    (((PMSubstrate.E8Values.Delta : ℝ) ^ 2 - (PMSubstrate.E8Values.nu : ℝ) ^ 2))

/-- E8 `|Vus| = s₁₂ c₂₃`. -/
def vusE8 : ℝ := PMFlavor.CKM.s12 * PMFlavor.CKM.c23

/-- E8 kaon width. -/
noncomputable def kaonWidthE8 : ℝ :=
  kaonWidthCKM kaonDecayConstantE8 vusE8

/-- E8 kaon lifetime. -/
noncomputable def kaonLifetimeE8 : ℝ := 1 / kaonWidthE8

/-- Broad enclosure of the E8 kaon decay constant in `m_e` units. -/
theorem kaonDecayConstantE8_bounds :
    (302.47 : ℝ) < kaonDecayConstantE8 ∧ kaonDecayConstantE8 < (302.48 : ℝ) := by
  unfold kaonDecayConstantE8 PMConstants.ElectroweakE8.vev
  rw [show (((PMSubstrate.E8Values.Delta : ℝ) ^ 2 -
      (PMSubstrate.E8Values.nu : ℝ) ^ 2)) = 1593 by
    norm_num [PMSubstrate.E8Values.Delta, PMSubstrate.E8Values.nu]]
  have h := PMConstants.JointConstants.vev_ratio_bounds
  constructor <;> nlinarith [h.1, h.2]

/-- Broad enclosure of `|V_us| = s₁₂ c₂₃`. -/
theorem vusE8_bounds : (0.2242 : ℝ) < vusE8 ∧ vusE8 < (0.2245 : ℝ) := by
  have hs := PMFlavor.CKM.s12_bounds
  have hc := PMFlavor.CKM.c23_bounds
  unfold vusE8
  constructor <;> nlinarith [hs.1, hs.2, hc.1, hc.2]

/-- Broad enclosure of the kaon two-body phase-space factor. -/
theorem kaonPhaseSpaceFactor_bounds :
    (0.910 : ℝ) < (1 - (muon / kaonPlus) ^ 2) ^ 2 ∧
      (1 - (muon / kaonPlus) ^ 2) ^ 2 < (0.911 : ℝ) := by
  have hp := kaonPlus_value
  have hm := muon_value
  have hpos : (0 : ℝ) < kaonPlus := lt_trans (by norm_num) hp.1
  have hr1 : (0.2138 : ℝ) < muon / kaonPlus := by
    rw [lt_div_iff₀ hpos]; nlinarith [hm.1, hp.2]
  have hr2 : muon / kaonPlus < (0.2141 : ℝ) := by
    rw [div_lt_iff₀ hpos]; nlinarith [hm.2, hp.1]
  constructor
  · nlinarith [sq_nonneg (muon / kaonPlus - 0.2138),
      sq_nonneg (0.2141 - muon / kaonPlus)]
  · have hsqlo : (0.0457 : ℝ) < (muon / kaonPlus) ^ 2 := by
      nlinarith [sq_nonneg (muon / kaonPlus - 0.2138), hr1]
    have hsqhi : (muon / kaonPlus) ^ 2 < (0.04584 : ℝ) := by
      nlinarith [sq_nonneg (0.2141 - muon / kaonPlus), hr2]
    nlinarith [hsqlo, hsqhi,
      sq_nonneg (1 - (muon / kaonPlus) ^ 2 - 0.9541),
      sq_nonneg (0.9543 - (1 - (muon / kaonPlus) ^ 2))]

set_option maxHeartbeats 400000 in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- Broad enclosure of the E8 kaon width in `m_e` units. -/
theorem kaonWidthE8_bounds :
    (6.1e-14 : ℝ) < kaonWidthE8 ∧ kaonWidthE8 < (6.47e-14 : ℝ) := by
  have hf := kaonDecayConstantE8_bounds
  have hV := vusE8_bounds
  have hF := PMElementaryParticles.MuonLifetime.fermiME_bounds_tight
  have hp := kaonPlus_value
  have hm := muon_value
  have hfac := kaonPhaseSpaceFactor_bounds
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  have hFpos : (0 : ℝ) < fermiME := lt_trans (by norm_num) hF.1
  have hfpos : (0 : ℝ) < kaonDecayConstantE8 := lt_trans (by norm_num) hf.1
  have hmpos : (0 : ℝ) < muon := lt_trans (by norm_num) hm.1
  have hppos : (0 : ℝ) < kaonPlus := lt_trans (by norm_num) hp.1
  have hVpos : (0 : ℝ) < vusE8 := lt_trans (by norm_num) hV.1
  have hfacpos : (0 : ℝ) < (1 - (muon / kaonPlus) ^ 2) ^ 2 :=
    lt_trans (by norm_num) hfac.1
  have hF2lo : (3.04e-12 : ℝ) ^ 2 < fermiME ^ 2 := by nlinarith [hF.1, hF.2]
  have hF2hi : fermiME ^ 2 < (3.05e-12 : ℝ) ^ 2 := by nlinarith [hF.1, hF.2]
  have hf2lo : (302.47 : ℝ) ^ 2 < kaonDecayConstantE8 ^ 2 := by nlinarith [hf.1, hf.2]
  have hf2hi : kaonDecayConstantE8 ^ 2 < (302.48 : ℝ) ^ 2 := by nlinarith [hf.1, hf.2]
  have hm2lo : (206.7682716 : ℝ) ^ 2 < muon ^ 2 := by nlinarith [hm.1, hm.2]
  have hm2hi : muon ^ 2 < (206.7682718 : ℝ) ^ 2 := by nlinarith [hm.1, hm.2]
  have hV2lo : (0.2242 : ℝ) ^ 2 < vusE8 ^ 2 := by nlinarith [hV.1, hV.2]
  have hV2hi : vusE8 ^ 2 < (0.2245 : ℝ) ^ 2 := by nlinarith [hV.1, hV.2]
  have hprodlo :
      (3.04e-12 : ℝ)^2 * (302.47:ℝ)^2 * 966 * (206.7682716:ℝ)^2 * 0.910 *
          (0.2242:ℝ)^2 <
        fermiME^2 * kaonDecayConstantE8^2 * kaonPlus * muon^2 *
          (1 - (muon / kaonPlus)^2)^2 * vusE8^2 := by
    gcongr <;> first
      | exact hF2lo | exact hf2lo | exact hp.1 | exact hm2lo | exact hfac.1 | exact hV2lo
      | exact hFpos | exact hfpos | exact hmpos | exact hppos | exact hfacpos | exact hVpos
  have hprodhi :
      fermiME^2 * kaonDecayConstantE8^2 * kaonPlus * muon^2 *
          (1 - (muon / kaonPlus)^2)^2 * vusE8^2 <
        (3.05e-12 : ℝ)^2 * (302.48:ℝ)^2 * 967 * (206.7682718:ℝ)^2 * 0.911 *
          (0.2245:ℝ)^2 := by
    gcongr <;> first
      | exact hF2hi | exact hf2hi | exact hp.2 | exact hm2hi | exact hfac.2 | exact hV2hi
      | exact hFpos | exact hfpos | exact hmpos | exact hppos | exact hfacpos | exact hVpos
  have hdenlo : (25 : ℝ) < 8 * Real.pi := by nlinarith [hpi1]
  have hdenhi : 8 * Real.pi < (26 : ℝ) := by nlinarith [hpi2]
  have hdenpos : (0 : ℝ) < 8 * Real.pi := by positivity
  unfold kaonWidthE8 kaonWidthCKM kaonWidth
  rw [div_mul_eq_mul_div]
  constructor
  · rw [lt_div_iff₀ hdenpos]
    nlinarith [hprodlo, hdenhi]
  · rw [div_lt_iff₀ hdenpos]
    nlinarith [hprodhi, hdenlo]

/-- Broad enclosure of the E8 kaon lifetime in `m_e⁻¹`. -/
theorem kaonLifetimeE8_bounds :
    (1.54e13 : ℝ) < kaonLifetimeE8 ∧ kaonLifetimeE8 < (1.64e13 : ℝ) := by
  have hw := kaonWidthE8_bounds
  have hwpos : (0 : ℝ) < kaonWidthE8 := lt_trans (by norm_num) hw.1
  unfold kaonLifetimeE8
  constructor
  · rw [lt_div_iff₀ hwpos]
    nlinarith [hw.2]
  · rw [div_lt_iff₀ hwpos]
    nlinarith [hw.1]

end PMElementaryParticles.KaonWidth
