import PMElementaryParticles.SharedUnits
import PMElementaryParticles.MuonLifetime
import PMElementaryParticles.TauE8
import Mathlib.Tactic

/-! **Comparison / unit conversion.**

Natural-unit lifetimes are in `m_e⁻¹`.  This module converts them to seconds
using the measured electron mass and `ħc`.  These are comparison inputs, not
E8-derived numbers.
-/

noncomputable section
namespace PMElementaryParticles.PhysicalUnits

open PMElementaryParticles.SharedUnits

/-- Speed of light in `fm/s` (unit conversion). -/
def cFmPerSecond : ℝ := 2.99792458e23

/-- Electron time unit `ħ/(m_e c²)` in seconds. -/
def electronTime : ℝ := hbarc / (me * cFmPerSecond)

theorem electronTime_pos : 0 < electronTime := by
  unfold electronTime cFmPerSecond hbarc me
  norm_num

/-- Broad certified enclosure of the electron time unit. -/
theorem electronTime_bounds :
    (1.2880e-21 : ℝ) < electronTime ∧ electronTime < 1.2882e-21 := by
  unfold electronTime cFmPerSecond hbarc me
  constructor <;> norm_num

/-- The electron time unit to `10⁻⁸`: `1.28808866–1.28808867 × 10⁻²¹` s. -/
theorem electronTime_tight :
    (1.28808866e-21 : ℝ) < electronTime ∧ electronTime < 1.28808867e-21 := by
  unfold electronTime cFmPerSecond hbarc me
  constructor <;> norm_num

/-- Muon lifetime in seconds. -/
def muonLifetimeSeconds : ℝ :=
  PMElementaryParticles.MuonLifetime.muonLifetime * electronTime

/-- Broad certified enclosure of the muon lifetime in seconds. -/
theorem muonLifetimeSeconds_bounds :
    (1.60e-6 : ℝ) < muonLifetimeSeconds ∧ muonLifetimeSeconds < 3.23e-6 := by
  have hm := PMElementaryParticles.MuonLifetime.muonLifetime_bounds
  have ht := electronTime_bounds
  have hmpos : (0 : ℝ) < PMElementaryParticles.MuonLifetime.muonLifetime :=
    lt_trans (by norm_num) hm.1
  have htpos : (0 : ℝ) < electronTime := lt_trans (by norm_num) ht.1
  have hprodlo := mul_lt_mul'' hm.1 ht.1 (by norm_num) (by norm_num)
  have hprodhi := mul_lt_mul'' hm.2 ht.2 (le_of_lt hmpos) (le_of_lt htpos)
  unfold muonLifetimeSeconds
  constructor <;> nlinarith [hprodlo, hprodhi]

/-- Tree-level muon lifetime `192π³/(G_F² m_μ⁵)` in seconds, to about `4×10⁻⁶`.

This is the E8 `G_F` and E8 `m_μ/m_e` in the massless-pair tree formula. The measured
`2.1969811 µs` includes the QED radiative factor `1 − (α/2π)(π² − 25/4)` and the
`m_e²/m_μ²` phase-space factor (together `≈ 0.99562`), which are not part of this row. -/
theorem muonLifetimeSeconds_tight :
    (2.187343e-6 : ℝ) < muonLifetimeSeconds ∧ muonLifetimeSeconds < 2.187352e-6 := by
  have hf := PMElementaryParticles.SharedUnits.fermiME_tight
  have hm := PMElementaryParticles.LeptonMasses.muon_value
  have hp1 : (3.14159265358979 : ℝ) < Real.pi := by linarith [Real.pi_gt_d20]
  have hp2 : Real.pi < (3.14159265358980 : ℝ) := by linarith [Real.pi_lt_d20]
  have he := electronTime_tight
  have hmpos : (0 : ℝ) < PMElementaryParticles.LeptonMasses.muon := by linarith [hm.1]
  have hfpos : (0 : ℝ) < fermiME := by linarith [hf.1]
  have hppos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hG2lo : (3.0456453e-12 : ℝ) ^ 2 < fermiME ^ 2 :=
    pow_lt_pow_left₀ hf.1 (by norm_num) (by norm_num)
  have hG2hi : fermiME ^ 2 < (3.0456507e-12 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hf.2 hfpos.le (by norm_num)
  have hm5lo : (206.7682716 : ℝ) ^ 5 < PMElementaryParticles.LeptonMasses.muon ^ 5 :=
    pow_lt_pow_left₀ hm.1 (by norm_num) (by norm_num)
  have hm5hi : PMElementaryParticles.LeptonMasses.muon ^ 5 < (206.7682718 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ hm.2 hmpos.le (by norm_num)
  have hp3lo : (3.14159265358979 : ℝ) ^ 3 < Real.pi ^ 3 :=
    pow_lt_pow_left₀ hp1 (by norm_num) (by norm_num)
  have hp3hi : Real.pi ^ 3 < (3.14159265358980 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hp2 hppos.le (by norm_num)
  have hDpos : (0 : ℝ) < fermiME ^ 2 * PMElementaryParticles.LeptonMasses.muon ^ 5 :=
    mul_pos (pow_pos hfpos 2) (pow_pos hmpos 5)
  have hDlo : (3.0456453e-12 : ℝ) ^ 2 * (206.7682716 : ℝ) ^ 5 <
      fermiME ^ 2 * PMElementaryParticles.LeptonMasses.muon ^ 5 :=
    mul_lt_mul'' hG2lo hm5lo (by norm_num) (by norm_num)
  have hDhi : fermiME ^ 2 * PMElementaryParticles.LeptonMasses.muon ^ 5 <
      (3.0456507e-12 : ℝ) ^ 2 * (206.7682718 : ℝ) ^ 5 :=
    mul_lt_mul'' hG2hi hm5hi (by positivity) (pow_pos hmpos 5).le
  have hτ : muonLifetimeSeconds =
      192 * Real.pi ^ 3 / (fermiME ^ 2 * PMElementaryParticles.LeptonMasses.muon ^ 5) *
        electronTime := by
    unfold muonLifetimeSeconds
    rw [PMElementaryParticles.MuonLifetime.muonLifetime_eq]
    unfold PMElementaryParticles.MuonLifetime.muonWidth
    rw [one_div_div]
  have hXlo : 192 * (3.14159265358979 : ℝ) ^ 3 / ((3.0456507e-12 : ℝ) ^ 2 * (206.7682718 : ℝ) ^ 5) <
      192 * Real.pi ^ 3 / (fermiME ^ 2 * PMElementaryParticles.LeptonMasses.muon ^ 5) := by
    rw [div_lt_div_iff₀ (by norm_num) hDpos]
    have := mul_lt_mul'' hp3lo hDhi (by norm_num) hDpos.le
    linarith
  have hXhi : 192 * Real.pi ^ 3 / (fermiME ^ 2 * PMElementaryParticles.LeptonMasses.muon ^ 5) <
      192 * (3.14159265358980 : ℝ) ^ 3 / ((3.0456453e-12 : ℝ) ^ 2 * (206.7682716 : ℝ) ^ 5) := by
    rw [div_lt_div_iff₀ hDpos (by norm_num)]
    have := mul_lt_mul'' hp3hi hDlo (pow_pos hppos 3).le (by norm_num)
    linarith
  have hXpos : (0 : ℝ) <
      192 * Real.pi ^ 3 / (fermiME ^ 2 * PMElementaryParticles.LeptonMasses.muon ^ 5) :=
    div_pos (by positivity) hDpos
  rw [hτ]
  constructor
  · calc (2.187343e-6 : ℝ)
        < 192 * (3.14159265358979 : ℝ) ^ 3 /
            ((3.0456507e-12 : ℝ) ^ 2 * (206.7682718 : ℝ) ^ 5) * 1.28808866e-21 := by norm_num
      _ < _ := mul_lt_mul'' hXlo he.1 (by norm_num) (by norm_num)
  · calc _ < 192 * (3.14159265358980 : ℝ) ^ 3 /
            ((3.0456453e-12 : ℝ) ^ 2 * (206.7682716 : ℝ) ^ 5) * 1.28808867e-21 :=
          mul_lt_mul'' hXhi he.2 hXpos.le (lt_trans (by norm_num) he.1).le
      _ < (2.187352e-6 : ℝ) := by norm_num

/-- E8-input tau lifetime in seconds. -/
def tauLifetimeSeconds : ℝ :=
  PMElementaryParticles.TauE8.tauLifetimeE8 * electronTime

/-- Broad certified enclosure of the E8-input tau lifetime in seconds. -/
theorem tauLifetimeSeconds_bounds :
    (2.06e-13 : ℝ) < tauLifetimeSeconds ∧ tauLifetimeSeconds < 4.39e-13 := by
  have ht := PMElementaryParticles.TauE8.tauLifetimeE8_bounds
  have he := electronTime_bounds
  have htpos : (0 : ℝ) < PMElementaryParticles.TauE8.tauLifetimeE8 :=
    lt_trans (by norm_num) ht.1
  have hepos : (0 : ℝ) < electronTime := lt_trans (by norm_num) he.1
  have hprodlo := mul_lt_mul'' ht.1 he.1 (by norm_num) (by norm_num)
  have hprodhi := mul_lt_mul'' ht.2 he.2 (le_of_lt htpos) (le_of_lt hepos)
  unfold tauLifetimeSeconds
  constructor <;> nlinarith [hprodlo, hprodhi]

end PMElementaryParticles.PhysicalUnits
