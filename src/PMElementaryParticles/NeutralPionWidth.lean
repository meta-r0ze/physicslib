import PMElementaryParticles.PionWidth
import PMElementaryParticles.CompositeMasses
import PMConstants.CurrentConstants
import Mathlib.Tactic

/-! **Comparison / E8-input check.**

Neutral-pion two-photon width:

```
Γ(π⁰ → γγ) = α² m_π⁰³ / (32π³ fπ²)
```

With `fπ` in the `130 MeV` convention, the identical-photon factor is `32`.
`α`, `m_π⁰`, and `fπ` are E8 inputs.
-/

noncomputable section
namespace PMElementaryParticles.NeutralPionWidth

open PMElementaryParticles.PionWidth
open PMElementaryParticles.CompositeMasses

/-- E8-input neutral-pion width. -/
noncomputable def neutralPionWidthE8 : ℝ :=
  (PMConstants.CurrentConstants.alpha ^ 2 * pion0 ^ 3) /
    (32 * Real.pi ^ 3 * pionDecayConstantE8 ^ 2)

/-- E8-input neutral-pion lifetime. -/
noncomputable def neutralPionLifetimeE8 : ℝ :=
  1 / neutralPionWidthE8

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- Broad enclosure of the neutral-pion width in `m_e` units. -/
theorem neutralPionWidthE8_bounds :
    (1.5e-5 : ℝ) < neutralPionWidthE8 ∧ neutralPionWidthE8 < (1.55e-5 : ℝ) := by
  have ha := PMConstants.CertifiedConstants.alpha_bounds
  have hm := CompositeMasses.pion0_value
  have hf := PionWidth.pionDecayConstantE8_bounds
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  have hapos : (0 : ℝ) < PMConstants.CurrentConstants.alpha := lt_trans (by norm_num) ha.1
  have hmpos : (0 : ℝ) < pion0 := lt_trans (by norm_num) hm.1
  have hfpos : (0 : ℝ) < pionDecayConstantE8 := lt_trans (by norm_num) hf.1
  have hpipos : (0 : ℝ) < Real.pi := by positivity
  have ha2lo : (0.007297352562 : ℝ) ^ 2 < PMConstants.CurrentConstants.alpha ^ 2 := by
    nlinarith [ha.1, ha.2]
  have ha2hi : PMConstants.CurrentConstants.alpha ^ 2 < (0.007297352563 : ℝ) ^ 2 := by
    nlinarith [ha.1, ha.2]
  have hm3lo : (264.1 : ℝ) ^ 3 < pion0 ^ 3 := by
    exact pow_lt_pow_left₀ hm.1 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
  have hm3hi : pion0 ^ 3 < (264.2 : ℝ) ^ 3 := by
    exact pow_lt_pow_left₀ hm.2 (le_of_lt hmpos) (by norm_num : (3 : ℕ) ≠ 0)
  have hf2lo : (254 : ℝ) ^ 2 < pionDecayConstantE8 ^ 2 := by nlinarith [hf.1, hf.2]
  have hf2hi : pionDecayConstantE8 ^ 2 < (256 : ℝ) ^ 2 := by nlinarith [hf.1, hf.2]
  have hpi3lo : (3.1415926535 : ℝ) ^ 3 < Real.pi ^ 3 := by
    have h := pow_lt_pow_left₀ hpi1 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
    exact lt_trans (by norm_num) h
  have hpi3hi : Real.pi ^ 3 < (3.1415926536 : ℝ) ^ 3 := by
    have h := pow_lt_pow_left₀ hpi2 (le_of_lt hpipos) (by norm_num : (3 : ℕ) ≠ 0)
    exact lt_trans h (by norm_num)
  have hnumlo :
      (0.007297352562 : ℝ)^2 * (264.1:ℝ)^3 <
        PMConstants.CurrentConstants.alpha^2 * pion0^3 := by
    gcongr <;> first
      | exact ha2lo | exact hm3lo
      | exact hapos | exact hmpos
  have hnumhi :
      PMConstants.CurrentConstants.alpha^2 * pion0^3 <
        (0.007297352563 : ℝ)^2 * (264.2:ℝ)^3 := by
    gcongr <;> first
      | exact ha2hi | exact hm3hi
      | exact hapos | exact hmpos
  have hdenlo :
      32 * (3.1415926535 : ℝ)^3 * (254:ℝ)^2 <
        32 * Real.pi^3 * pionDecayConstantE8^2 := by
    gcongr <;> first
      | exact hpi3lo | exact hf2lo
      | norm_num | exact hpipos | exact hfpos
  have hdenhi :
      32 * Real.pi^3 * pionDecayConstantE8^2 <
        32 * (3.1415926536 : ℝ)^3 * (256:ℝ)^2 := by
    gcongr <;> first
      | exact hpi3hi | exact hf2hi
      | norm_num | exact hpipos | exact hfpos
  have hdenpos : (0 : ℝ) < 32 * Real.pi^3 * pionDecayConstantE8^2 := by positivity
  unfold neutralPionWidthE8
  constructor
  · rw [lt_div_iff₀ hdenpos]
    nlinarith [hnumlo, hdenhi]
  · rw [div_lt_iff₀ hdenpos]
    nlinarith [hnumhi, hdenlo]

/-- Broad enclosure of the neutral-pion lifetime in `m_e⁻¹`. -/
theorem neutralPionLifetimeE8_bounds :
    (6.4e4 : ℝ) < neutralPionLifetimeE8 ∧ neutralPionLifetimeE8 < (6.7e4 : ℝ) := by
  have hw := neutralPionWidthE8_bounds
  have hwpos : (0 : ℝ) < neutralPionWidthE8 := lt_trans (by norm_num) hw.1
  unfold neutralPionLifetimeE8
  constructor
  · rw [lt_div_iff₀ hwpos]
    nlinarith [hw.2]
  · rw [div_lt_iff₀ hwpos]
    nlinarith [hw.1]

end PMElementaryParticles.NeutralPionWidth
