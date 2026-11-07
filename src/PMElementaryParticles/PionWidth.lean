import PMElementaryParticles.LeptonMasses
import PMElementaryParticles.NeutronRate
import PMConstants.ElectroweakE8
import PMConstants.CurrentConstants
import PMConstants.JointConstants
import PMElementaryParticles.MuonLifetime
import PMSubstrate.E8Values
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! **Comparison / structural.**

Two-body charged-pion width:

```
Γ(π⁺ → μ⁺ν) = G_F² f_π² m_π m_μ² (1 − m_μ²/m_π²)² / (8π).
```

The pion decay constant `f_π` is still a supplied input.
-/

noncomputable section
namespace PMElementaryParticles.PionWidth

open PMElementaryParticles.LeptonMasses
open PMElementaryParticles.NeutronRate

def pionWidth (fPi : ℝ) : ℝ :=
  fermiME ^ 2 * fPi ^ 2 * pionPlus * muon ^ 2 *
    (1 - (muon / pionPlus) ^ 2) ^ 2 / (8 * Real.pi)

def pionLifetime (fPi : ℝ) : ℝ :=
  1 / pionWidth fPi

theorem pionLifetime_eq (fPi : ℝ) : pionLifetime fPi = 1 / pionWidth fPi := rfl

/-- E8 pion decay constant in `m_e` units:
`v/(Δ² + Δ − χ)` with `m_e = 1`. -/
noncomputable def pionDecayConstantE8 : ℝ :=
  PMConstants.ElectroweakE8.vev PMConstants.CurrentConstants.alpha 1 /
    (((PMSubstrate.E8Values.Delta : ℝ) ^ 2 +
      ((PMSubstrate.E8Values.Delta - PMSubstrate.E8Values.chi : Nat) : ℝ)))

/-- E8 pion width. -/
noncomputable def pionWidthE8 : ℝ := pionWidth pionDecayConstantE8

/-- E8 pion lifetime. -/
noncomputable def pionLifetimeE8 : ℝ := pionLifetime pionDecayConstantE8

/-- Broad enclosure of the E8 pion decay constant in `m_e` units. -/
theorem pionDecayConstantE8_bounds :
    (254 : ℝ) < pionDecayConstantE8 ∧ pionDecayConstantE8 < (256 : ℝ) := by
  unfold pionDecayConstantE8 PMConstants.ElectroweakE8.vev
  rw [show (((PMSubstrate.E8Values.Delta : ℝ) ^ 2 +
      ((PMSubstrate.E8Values.Delta - PMSubstrate.E8Values.chi : Nat) : ℝ))) = 1890 by
    norm_num [PMSubstrate.E8Values.Delta, PMSubstrate.E8Values.chi]]
  have h := PMConstants.JointConstants.vev_ratio_bounds
  constructor <;> nlinarith [h.1, h.2]

/-- Broad enclosure of the two-body phase-space factor. -/
theorem pionPhaseSpaceFactor_bounds :
    (0.18 : ℝ) < (1 - (muon / pionPlus) ^ 2) ^ 2 ∧
      (1 - (muon / pionPlus) ^ 2) ^ 2 < (0.19 : ℝ) := by
  have hp := pionPlus_value
  have hm := muon_value
  have hpos : (0 : ℝ) < pionPlus := lt_trans (by norm_num) hp.1
  have hr1 : (0.756 : ℝ) < muon / pionPlus := by
    rw [lt_div_iff₀ hpos]; nlinarith [hm.1, hp.2]
  have hr2 : muon / pionPlus < (0.758 : ℝ) := by
    rw [div_lt_iff₀ hpos]; nlinarith [hm.2, hp.1]
  constructor
  · nlinarith [sq_nonneg (muon / pionPlus - 0.756),
      sq_nonneg (0.758 - muon / pionPlus)]
  · have hsqlo : (0.5715 : ℝ) < (muon / pionPlus) ^ 2 := by
      nlinarith [sq_nonneg (muon / pionPlus - 0.756), hr1]
    have hsqhi : (muon / pionPlus) ^ 2 < (0.5746 : ℝ) := by
      nlinarith [sq_nonneg (0.758 - muon / pionPlus), hr2]
    nlinarith [hsqlo, hsqhi,
      sq_nonneg (1 - (muon / pionPlus) ^ 2 - 0.4254),
      sq_nonneg (0.4285 - (1 - (muon / pionPlus) ^ 2))]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- Broad enclosure of the charged-pion width in `m_e` units. -/
theorem pionWidthE8_bounds :
    (4e-14 : ℝ) < pionWidthE8 ∧ pionWidthE8 < (6e-14 : ℝ) := by
  have hf := pionDecayConstantE8_bounds
  have hF := PMElementaryParticles.MuonLifetime.fermiME_bounds
  have hp := pionPlus_value
  have hm := muon_value
  have hfac := pionPhaseSpaceFactor_bounds
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  have hFpos : (0 : ℝ) < fermiME := lt_trans (by norm_num) hF.1
  have hfpos : (0 : ℝ) < pionDecayConstantE8 := lt_trans (by norm_num) hf.1
  have hmpos : (0 : ℝ) < muon := lt_trans (by norm_num) hm.1
  have hppos : (0 : ℝ) < pionPlus := lt_trans (by norm_num) hp.1
  have hfacpos : (0 : ℝ) < (1 - (muon / pionPlus) ^ 2) ^ 2 :=
    lt_trans (by norm_num) hfac.1
  have hF2lo : (2.9e-12 : ℝ) ^ 2 < fermiME ^ 2 := by nlinarith [hF.1, hF.2]
  have hF2hi : fermiME ^ 2 < (3.2e-12 : ℝ) ^ 2 := by nlinarith [hF.1, hF.2]
  have hf2lo : (254 : ℝ) ^ 2 < pionDecayConstantE8 ^ 2 := by nlinarith [hf.1, hf.2]
  have hf2hi : pionDecayConstantE8 ^ 2 < (256 : ℝ) ^ 2 := by nlinarith [hf.1, hf.2]
  have hm2lo : (206.7682716 : ℝ) ^ 2 < muon ^ 2 := by nlinarith [hm.1, hm.2]
  have hm2hi : muon ^ 2 < (206.7682718 : ℝ) ^ 2 := by nlinarith [hm.1, hm.2]
  have hprodlo :
      (2.9e-12 : ℝ)^2 * (254:ℝ)^2 * 273.1 * (206.7682716:ℝ)^2 * 0.18 <
        fermiME^2 * pionDecayConstantE8^2 * pionPlus * muon^2 *
          (1 - (muon / pionPlus)^2)^2 := by
    gcongr <;> first
      | exact hF2lo | exact hf2lo | exact hp.1 | exact hm2lo | exact hfac.1
      | exact hFpos | exact hfpos | exact hmpos | exact hppos | exact hfacpos
  have hprodhi :
      fermiME^2 * pionDecayConstantE8^2 * pionPlus * muon^2 *
          (1 - (muon / pionPlus)^2)^2 <
        (3.2e-12 : ℝ)^2 * (256:ℝ)^2 * 273.2 * (206.7682718:ℝ)^2 * 0.19 := by
    gcongr <;> first
      | exact hF2hi | exact hf2hi | exact hp.2 | exact hm2hi | exact hfac.2
      | exact hFpos | exact hfpos | exact hmpos | exact hppos | exact hfacpos
  have hdenlo : (25 : ℝ) < 8 * Real.pi := by nlinarith [hpi1]
  have hdenhi : 8 * Real.pi < (26 : ℝ) := by nlinarith [hpi2]
  have hdenpos : (0 : ℝ) < 8 * Real.pi := by positivity
  unfold pionWidthE8 pionWidth
  constructor
  · rw [lt_div_iff₀ hdenpos]
    nlinarith [hprodlo, hdenhi]
  · rw [div_lt_iff₀ hdenpos]
    nlinarith [hprodhi, hdenlo]

/-- Broad enclosure of the charged-pion lifetime in `m_e⁻¹`. -/
theorem pionLifetimeE8_bounds :
    (1.6e13 : ℝ) < pionLifetimeE8 ∧ pionLifetimeE8 < (2.5e13 : ℝ) := by
  have hw := pionWidthE8_bounds
  have hwpos : (0 : ℝ) < pionWidthE8 := lt_trans (by norm_num) hw.1
  unfold pionLifetimeE8 pionLifetime
  change (1.6e13 : ℝ) < 1 / pionWidthE8 ∧ 1 / pionWidthE8 < (2.5e13 : ℝ)
  constructor
  · rw [lt_div_iff₀ hwpos]
    nlinarith [hw.2]
  · rw [div_lt_iff₀ hwpos]
    nlinarith [hw.1]

/-- Pion two-body width for a daughter of mass `ml` in `m_e` units. -/
noncomputable def pionWidthTo (fPi ml : ℝ) : ℝ :=
  fermiME ^ 2 * fPi ^ 2 * pionPlus * ml ^ 2 *
    (1 - (ml / pionPlus) ^ 2) ^ 2 / (8 * Real.pi)

/-- Pion electron width with E8 `fπ`; electron mass is `1` in `m_e` units. -/
noncomputable def pionElectronWidthE8 : ℝ :=
  pionWidthTo pionDecayConstantE8 1

/-- Pion electron lifetime. -/
noncomputable def pionElectronLifetimeE8 : ℝ :=
  1 / pionElectronWidthE8

end PMElementaryParticles.PionWidth
