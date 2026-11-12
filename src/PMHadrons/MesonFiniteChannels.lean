import PMHadrons.MesonMasses
import PMElementaryParticles.BetaLattice
import PMHadrons.PionWidth
import PMHadrons.KaonWidth
import PMHadrons.NeutralPionWidth
import PMElementaryParticles.PhysicalUnits
import PMElementaryParticles.Values
import PMSubstrate.E8Margin
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Finite spectral channels for the meson decays

This is the minimal-cube analogue of `LeptonLifetime` and `NeutronPrediction`.
The cutoff is set to the parent mass in `m_e` units.  For π⁺, K⁺ and π⁰ this
cutoff is far above the universal bound `12`, so every `3×3×3` mode is open and
the finite spectral fraction is exactly one.  The finite channel therefore
reduces to the existing continuum width; this module records that reduction
explicitly rather than silently assuming it.

The underlying coherent-action form is in
`PersistenceMechanics.EffectiveAction`: population decay comes from
`exp(−β·cost)`, while phase loss is the separate `decoherenceRate`.  The
spectral fraction here is the population/margin factor; it does not change the
phase-loss channel.
-/

noncomputable section
namespace PMHadrons
open PMElementaryParticles

open PMElementaryParticles
open PMHadrons

/-- Minimal volume-persistent cube, as in the neutron channel. -/
def mesonFiniteCube : Nat := 3

/-- Charged-pion cutoff: the parent mass in `m_e` units. -/
def pionFiniteCutoff : ℝ := MesonMasses.pionPlus

/-- Charged-kaon cutoff: the parent mass in `m_e` units. -/
def kaonFiniteCutoff : ℝ := CompositeMasses.kaonPlus

/-- Neutral-pion cutoff: the parent mass in `m_e` units. -/
def neutralPionFiniteCutoff : ℝ := CompositeMasses.pion0

theorem pionFiniteCutoff_gt_twelve : (12 : ℝ) < pionFiniteCutoff := by
  unfold pionFiniteCutoff
  linarith [MesonMasses.pionPlus_value.1]

theorem kaonFiniteCutoff_gt_twelve : (12 : ℝ) < kaonFiniteCutoff := by
  unfold kaonFiniteCutoff
  linarith [CompositeMasses.kaonPlus_value.1]

theorem neutralPionFiniteCutoff_gt_twelve : (12 : ℝ) < neutralPionFiniteCutoff := by
  unfold neutralPionFiniteCutoff
  linarith [CompositeMasses.pion0_value.1]

theorem pion_openModes :
    betaOpenModes mesonFiniteCube pionFiniteCutoff = Finset.univ := by
  unfold mesonFiniteCube
  exact betaOpenModes_eq_univ_of_twelve_le (le_of_lt pionFiniteCutoff_gt_twelve)

theorem kaon_openModes :
    betaOpenModes mesonFiniteCube kaonFiniteCutoff = Finset.univ := by
  unfold mesonFiniteCube
  exact betaOpenModes_eq_univ_of_twelve_le (le_of_lt kaonFiniteCutoff_gt_twelve)

theorem neutralPion_openModes :
    betaOpenModes mesonFiniteCube neutralPionFiniteCutoff = Finset.univ := by
  unfold mesonFiniteCube
  exact betaOpenModes_eq_univ_of_twelve_le (le_of_lt neutralPionFiniteCutoff_gt_twelve)

/-- Finite spectral fraction for the charged pion. -/
def pionSpectralFraction : ℝ :=
  betaSpectralRateCutoff 1 1 mesonFiniteCube pionFiniteCutoff

/-- Finite spectral fraction for the charged kaon. -/
def kaonSpectralFraction : ℝ :=
  betaSpectralRateCutoff 1 1 mesonFiniteCube kaonFiniteCutoff

/-- Finite spectral fraction for the neutral pion. -/
def neutralPionSpectralFraction : ℝ :=
  betaSpectralRateCutoff 1 1 mesonFiniteCube neutralPionFiniteCutoff

theorem pionSpectralFraction_eq_one : pionSpectralFraction = 1 := by
  unfold pionSpectralFraction mesonFiniteCube
  exact betaSpectralRateCutoff_eq_one_of_openModes_eq_univ (by norm_num) pion_openModes

theorem kaonSpectralFraction_eq_one : kaonSpectralFraction = 1 := by
  unfold kaonSpectralFraction mesonFiniteCube
  exact betaSpectralRateCutoff_eq_one_of_openModes_eq_univ (by norm_num) kaon_openModes

theorem neutralPionSpectralFraction_eq_one : neutralPionSpectralFraction = 1 := by
  unfold neutralPionSpectralFraction mesonFiniteCube
  exact betaSpectralRateCutoff_eq_one_of_openModes_eq_univ (by norm_num) neutralPion_openModes

/-- Finite-channel charged-pion width. -/
def pionFiniteWidth : ℝ :=
  PionWidth.pionWidthE8 * pionSpectralFraction

/-- Finite-channel charged-kaon width. -/
def kaonFiniteWidth : ℝ :=
  KaonWidth.kaonWidthE8 * kaonSpectralFraction

/-- Finite-channel neutral-pion width. -/
def neutralPionFiniteWidth : ℝ :=
  NeutralPionWidth.neutralPionWidthE8 * neutralPionSpectralFraction

theorem pionFiniteWidth_eq_continuum : pionFiniteWidth = PionWidth.pionWidthE8 := by
  unfold pionFiniteWidth
  rw [pionSpectralFraction_eq_one, mul_one]

theorem kaonFiniteWidth_eq_continuum : kaonFiniteWidth = KaonWidth.kaonWidthE8 := by
  unfold kaonFiniteWidth
  rw [kaonSpectralFraction_eq_one, mul_one]

theorem neutralPionFiniteWidth_eq_continuum :
    neutralPionFiniteWidth = NeutralPionWidth.neutralPionWidthE8 := by
  unfold neutralPionFiniteWidth
  rw [neutralPionSpectralFraction_eq_one, mul_one]

/-- Finite-channel charged-pion lifetime. -/
def pionFiniteLifetime : ℝ :=
  PionWidth.pionLifetimeE8 / pionSpectralFraction

/-- Finite-channel charged-kaon lifetime. -/
def kaonFiniteLifetime : ℝ :=
  KaonWidth.kaonLifetimeE8 / kaonSpectralFraction

/-- Finite-channel neutral-pion lifetime. -/
def neutralPionFiniteLifetime : ℝ :=
  NeutralPionWidth.neutralPionLifetimeE8 / neutralPionSpectralFraction

theorem pionFiniteLifetime_eq_continuum :
    pionFiniteLifetime = PionWidth.pionLifetimeE8 := by
  unfold pionFiniteLifetime
  rw [pionSpectralFraction_eq_one, div_one]

theorem kaonFiniteLifetime_eq_continuum :
    kaonFiniteLifetime = KaonWidth.kaonLifetimeE8 := by
  unfold kaonFiniteLifetime
  rw [kaonSpectralFraction_eq_one, div_one]

theorem neutralPionFiniteLifetime_eq_continuum :
    neutralPionFiniteLifetime = NeutralPionWidth.neutralPionLifetimeE8 := by
  unfold neutralPionFiniteLifetime
  rw [neutralPionSpectralFraction_eq_one, div_one]

/-- Certified finite-channel pion width enclosure. -/
theorem pionFiniteWidth_bounds :
    (4.9e-14 : ℝ) < pionFiniteWidth ∧ pionFiniteWidth < (5.16e-14 : ℝ) := by
  rw [pionFiniteWidth_eq_continuum]
  exact PionWidth.pionWidthE8_bounds

/-- Certified finite-channel pion lifetime enclosure. -/
theorem pionFiniteLifetime_bounds :
    (1.9e13 : ℝ) < pionFiniteLifetime ∧ pionFiniteLifetime < (2.05e13 : ℝ) := by
  rw [pionFiniteLifetime_eq_continuum]
  exact PionWidth.pionLifetimeE8_bounds

/-- Certified finite-channel kaon width enclosure. -/
theorem kaonFiniteWidth_bounds :
    (6.1e-14 : ℝ) < kaonFiniteWidth ∧ kaonFiniteWidth < (6.47e-14 : ℝ) := by
  rw [kaonFiniteWidth_eq_continuum]
  exact KaonWidth.kaonWidthE8_bounds

/-- Certified finite-channel kaon lifetime enclosure. -/
theorem kaonFiniteLifetime_bounds :
    (1.54e13 : ℝ) < kaonFiniteLifetime ∧ kaonFiniteLifetime < (1.64e13 : ℝ) := by
  rw [kaonFiniteLifetime_eq_continuum]
  exact KaonWidth.kaonLifetimeE8_bounds

/-- Certified finite-channel neutral-pion width enclosure. -/
theorem neutralPionFiniteWidth_bounds :
    (1.52e-5 : ℝ) < neutralPionFiniteWidth ∧ neutralPionFiniteWidth < (1.523e-5 : ℝ) := by
  rw [neutralPionFiniteWidth_eq_continuum]
  exact PMHadrons.NeutralPionWidth.neutralPionWidthE8_bounds

/-- Certified finite-channel neutral-pion lifetime enclosure. -/
theorem neutralPionFiniteLifetime_bounds :
    (6.56e4 : ℝ) < neutralPionFiniteLifetime ∧ neutralPionFiniteLifetime < (6.58e4 : ℝ) := by
  rw [neutralPionFiniteLifetime_eq_continuum]
  exact PMHadrons.NeutralPionWidth.neutralPionLifetimeE8_bounds

/-- Finite-channel pion lifetime in seconds. -/
def pionFiniteLifetimeSeconds : ℝ :=
  pionFiniteLifetime * PMElementaryParticles.PhysicalUnits.electronTime

/-- Finite-channel kaon lifetime in seconds. -/
def kaonFiniteLifetimeSeconds : ℝ :=
  kaonFiniteLifetime * PMElementaryParticles.PhysicalUnits.electronTime

/-- Finite-channel neutral-pion lifetime in seconds. -/
def neutralPionFiniteLifetimeSeconds : ℝ :=
  neutralPionFiniteLifetime * PMElementaryParticles.PhysicalUnits.electronTime

theorem pionFiniteLifetimeSeconds_bounds :
    (2.44e-8 : ℝ) < pionFiniteLifetimeSeconds ∧
      pionFiniteLifetimeSeconds < (2.65e-8 : ℝ) := by
  have hl := pionFiniteLifetime_bounds
  have he := PMElementaryParticles.PhysicalUnits.electronTime_bounds
  have hlpos : (0 : ℝ) < pionFiniteLifetime := lt_trans (by norm_num) hl.1
  have hepos : (0 : ℝ) < PMElementaryParticles.PhysicalUnits.electronTime :=
    lt_trans (by norm_num) he.1
  have hlo := mul_lt_mul'' hl.1 he.1 (by norm_num) (by norm_num)
  have hhi := mul_lt_mul'' hl.2 he.2 (le_of_lt hlpos) (le_of_lt hepos)
  unfold pionFiniteLifetimeSeconds
  constructor <;> nlinarith [hlo, hhi]

theorem kaonFiniteLifetimeSeconds_bounds :
    (1.98e-8 : ℝ) < kaonFiniteLifetimeSeconds ∧
      kaonFiniteLifetimeSeconds < (2.12e-8 : ℝ) := by
  have hl := kaonFiniteLifetime_bounds
  have he := PMElementaryParticles.PhysicalUnits.electronTime_bounds
  have hlpos : (0 : ℝ) < kaonFiniteLifetime := lt_trans (by norm_num) hl.1
  have hepos : (0 : ℝ) < PMElementaryParticles.PhysicalUnits.electronTime :=
    lt_trans (by norm_num) he.1
  have hlo := mul_lt_mul'' hl.1 he.1 (by norm_num) (by norm_num)
  have hhi := mul_lt_mul'' hl.2 he.2 (le_of_lt hlpos) (le_of_lt hepos)
  unfold kaonFiniteLifetimeSeconds
  constructor <;> nlinarith [hlo, hhi]

theorem neutralPionFiniteLifetimeSeconds_bounds :
    (8.44e-17 : ℝ) < neutralPionFiniteLifetimeSeconds ∧
      neutralPionFiniteLifetimeSeconds < (8.48e-17 : ℝ) := by
  have hl := neutralPionFiniteLifetime_bounds
  have he := PMElementaryParticles.PhysicalUnits.electronTime_bounds
  have hlpos : (0 : ℝ) < neutralPionFiniteLifetime := lt_trans (by norm_num) hl.1
  have hepos : (0 : ℝ) < PMElementaryParticles.PhysicalUnits.electronTime :=
    lt_trans (by norm_num) he.1
  have hlo := mul_lt_mul'' hl.1 he.1 (by norm_num) (by norm_num)
  have hhi := mul_lt_mul'' hl.2 he.2 (le_of_lt hlpos) (le_of_lt hepos)
  unfold neutralPionFiniteLifetimeSeconds
  constructor <;> nlinarith [hlo, hhi]

/-! ## Charged pion after the pion-channel margin

`PMSubstrate.E8Margin.pionMargin = (Δ+ν+σ)/(Δ+ν+σ+χ) = 32/33` lengthens the two-body lifetime
by `33/32`. With the E8 `G_F`, `f_π = v/1890`, `m_π` and `m_μ` this gives `2.6019 × 10⁻⁸ s`.
The SM writes the same step as `|V_ud|²(1+δ_rad) ≈ 0.970` on the rate; `32/33 = 0.9697`. -/

/-- Pion lifetime after the pion-channel margin, in seconds. -/
def pionLifetimeCorrectedSeconds : ℝ :=
  PMSubstrate.E8Margin.pionCorrectedLifetime PionWidth.pionLifetimeE8 *
    PMElementaryParticles.PhysicalUnits.electronTime

/-- **The margin-corrected E8 pion lifetime is between `2.60188` and `2.60192 × 10⁻⁸` s.** -/
theorem pionLifetimeCorrectedSeconds_bounds :
    (2.60188e-8 : ℝ) < pionLifetimeCorrectedSeconds ∧
      pionLifetimeCorrectedSeconds < 2.60192e-8 := by
  have hS : pionLifetimeCorrectedSeconds =
      33 / 4 * Real.pi * PMElementaryParticles.PhysicalUnits.electronTime /
        (PMElementaryParticles.SharedUnits.fermiME ^ 2 * PionWidth.pionDecayConstantE8 ^ 2 *
          MesonMasses.pionPlus * PMElementaryParticles.LeptonMasses.muon ^ 2 *
          (1 - (PMElementaryParticles.LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2) := by
    unfold pionLifetimeCorrectedSeconds PMSubstrate.E8Margin.pionCorrectedLifetime
      PionWidth.pionLifetimeE8 PionWidth.pionLifetime PionWidth.pionWidth
    rw [PMSubstrate.E8Margin.pionMargin_eq]
    generalize PMElementaryParticles.SharedUnits.fermiME ^ 2 * PionWidth.pionDecayConstantE8 ^ 2 *
          MesonMasses.pionPlus * PMElementaryParticles.LeptonMasses.muon ^ 2 *
          (1 - (PMElementaryParticles.LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 = N
    rw [one_div_div]
    ring
  -- `G_F` in `m_e⁻²`
  have hG := PMElementaryParticles.Values.fermiME_tight
  -- `f_π = v/1890`
  have hf : (254.9416992 : ℝ) < PionWidth.pionDecayConstantE8 ∧
      PionWidth.pionDecayConstantE8 < (254.9416993 : ℝ) := by
    unfold PionWidth.pionDecayConstantE8 PMConstants.Values.vev PMConstants.ElectroweakE8.vev
    rw [show (((PMSubstrate.E8Values.Delta : ℝ) ^ 2 +
        ((PMSubstrate.E8Values.Delta - PMSubstrate.E8Values.chi : Nat) : ℝ))) = 1890 by
      norm_num [PMSubstrate.E8Values.Delta, PMSubstrate.E8Values.chi]]
    have h := PMConstants.Values.vev_ratio_bounds
    constructor <;> nlinarith [h.1, h.2]
  -- `m_π`, `m_μ`
  have hmp : (273.13236 : ℝ) < MesonMasses.pionPlus ∧ MesonMasses.pionPlus < 273.13251 := by
    have h := MesonMasses.pionPlus_mev_value
    simp only [PMElementaryParticles.SharedUnits.me] at h
    constructor <;> linarith [h.1, h.2]
  have hm := PMElementaryParticles.LeptonMasses.muon_value
  have hGpos : (0 : ℝ) < PMElementaryParticles.SharedUnits.fermiME := by linarith [hG.1]
  have hfpos : (0 : ℝ) < PionWidth.pionDecayConstantE8 := by linarith [hf.1]
  have hmppos : (0 : ℝ) < MesonMasses.pionPlus := by linarith [hmp.1]
  have hmupos : (0 : ℝ) < PMElementaryParticles.LeptonMasses.muon := by linarith [hm.1]
  -- phase-space factor `(1 − (m_μ/m_π)²)²`
  have hr1 : (0.7570254 : ℝ) <
      PMElementaryParticles.LeptonMasses.muon / MesonMasses.pionPlus := by
    rw [lt_div_iff₀ hmppos]; linarith [hm.1, hmp.2]
  have hr2 : PMElementaryParticles.LeptonMasses.muon / MesonMasses.pionPlus <
      (0.7570260 : ℝ) := by
    rw [div_lt_iff₀ hmppos]; linarith [hm.2, hmp.1]
  have hrpos : (0 : ℝ) < PMElementaryParticles.LeptonMasses.muon / MesonMasses.pionPlus :=
    div_pos hmupos hmppos
  have hq1 := pow_lt_pow_left₀ hr1 (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)
  have hq2 := pow_lt_pow_left₀ hr2 hrpos.le (by norm_num : (2 : ℕ) ≠ 0)
  have hF1 : (0.1822535 : ℝ) <
      (1 - (PMElementaryParticles.LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 := by
    have h1 : (1 - (0.7570260 : ℝ) ^ 2) <
        1 - (PMElementaryParticles.LeptonMasses.muon / MesonMasses.pionPlus) ^ 2 := by
      linarith [hq2]
    have h2 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)
    have h3 : (0.1822535 : ℝ) < (1 - (0.7570260 : ℝ) ^ 2) ^ 2 := by norm_num
    linarith
  have hF2 : (1 - (PMElementaryParticles.LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 <
      (0.1822544 : ℝ) := by
    have h1 : 1 - (PMElementaryParticles.LeptonMasses.muon / MesonMasses.pionPlus) ^ 2 <
        (1 - (0.7570254 : ℝ) ^ 2) := by
      linarith [hq1]
    have h0 : (0 : ℝ) ≤
        1 - (PMElementaryParticles.LeptonMasses.muon / MesonMasses.pionPlus) ^ 2 := by
      have : (0.7570260 : ℝ) ^ 2 < 1 := by norm_num
      linarith [hq2]
    have h2 := pow_lt_pow_left₀ h1 h0 (by norm_num : (2 : ℕ) ≠ 0)
    have h3 : (1 - (0.7570254 : ℝ) ^ 2) ^ 2 < 0.1822544 := by norm_num
    linarith
  have hFpos : (0 : ℝ) <
      (1 - (PMElementaryParticles.LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 := by
    linarith [hF1]
  -- the product `N = G² f² m_π m_μ² F`
  have hNlo : (3.0456453e-12 : ℝ) ^ 2 * (254.9416992 : ℝ) ^ 2 * 273.13236 *
        (206.7682716 : ℝ) ^ 2 * 0.1822535 <
      PMElementaryParticles.SharedUnits.fermiME ^ 2 * PionWidth.pionDecayConstantE8 ^ 2 *
        MesonMasses.pionPlus * PMElementaryParticles.LeptonMasses.muon ^ 2 *
        (1 - (PMElementaryParticles.LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 := by
    gcongr <;> first | exact hG.1 | exact hf.1 | exact hmp.1 | exact hm.1
  have hNhi :
      PMElementaryParticles.SharedUnits.fermiME ^ 2 * PionWidth.pionDecayConstantE8 ^ 2 *
        MesonMasses.pionPlus * PMElementaryParticles.LeptonMasses.muon ^ 2 *
        (1 - (PMElementaryParticles.LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 <
      (3.0456507e-12 : ℝ) ^ 2 * (254.9416993 : ℝ) ^ 2 * 273.13251 *
        (206.7682718 : ℝ) ^ 2 * 0.1822544 := by
    gcongr <;> first | exact hG.2 | exact hf.2 | exact hmp.2 | exact hm.2
  have hNpos : (0 : ℝ) <
      PMElementaryParticles.SharedUnits.fermiME ^ 2 * PionWidth.pionDecayConstantE8 ^ 2 *
        MesonMasses.pionPlus * PMElementaryParticles.LeptonMasses.muon ^ 2 *
        (1 - (PMElementaryParticles.LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 :=
    lt_trans (by norm_num) hNlo
  -- `π`, electron time
  have hp1 : (3.14159265358979 : ℝ) < Real.pi := by linarith [Real.pi_gt_d20]
  have hp2 : Real.pi < (3.14159265358980 : ℝ) := by linarith [Real.pi_lt_d20]
  have he := PMElementaryParticles.Values.electronTime_tight
  have hepos : (0 : ℝ) < PMElementaryParticles.PhysicalUnits.electronTime := by linarith [he.1]
  have hAlo := mul_lt_mul'' hp1 he.1 (by norm_num) (by norm_num)
  have hAhi := mul_lt_mul'' hp2 he.2 Real.pi_pos.le hepos.le
  rw [hS]
  constructor
  · rw [lt_div_iff₀ hNpos]
    calc (2.60188e-8 : ℝ) * _
        < 2.60188e-8 * ((3.0456507e-12 : ℝ) ^ 2 * (254.9416993 : ℝ) ^ 2 * 273.13251 *
            (206.7682718 : ℝ) ^ 2 * 0.1822544) := mul_lt_mul_of_pos_left hNhi (by norm_num)
      _ < 33 / 4 * ((3.14159265358979 : ℝ) * 1.28808866e-21) := by norm_num
      _ < 33 / 4 * (Real.pi * PMElementaryParticles.PhysicalUnits.electronTime) :=
          mul_lt_mul_of_pos_left hAlo (by norm_num)
      _ = _ := by ring
  · rw [div_lt_iff₀ hNpos]
    calc 33 / 4 * Real.pi * PMElementaryParticles.PhysicalUnits.electronTime
        = 33 / 4 * (Real.pi * PMElementaryParticles.PhysicalUnits.electronTime) := by ring
      _ < 33 / 4 * ((3.14159265358980 : ℝ) * 1.28808867e-21) :=
          mul_lt_mul_of_pos_left hAhi (by norm_num)
      _ < 2.60192e-8 * ((3.0456453e-12 : ℝ) ^ 2 * (254.9416992 : ℝ) ^ 2 * 273.13236 *
            (206.7682716 : ℝ) ^ 2 * 0.1822535) := by norm_num
      _ < 2.60192e-8 * _ := mul_lt_mul_of_pos_left hNlo (by norm_num)

end PMHadrons
