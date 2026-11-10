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
