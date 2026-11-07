import PMAtoms.BetaLattice
import PMElementaryParticles.PionWidth
import PMElementaryParticles.KaonWidth
import PMElementaryParticles.NeutralPionWidth
import PMElementaryParticles.PhysicalUnits
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
namespace PMAtoms

open PMElementaryParticles

/-- Minimal volume-persistent cube, as in the neutron channel. -/
def mesonFiniteCube : Nat := 3

/-- Charged-pion cutoff: the parent mass in `m_e` units. -/
def pionFiniteCutoff : ℝ := LeptonMasses.pionPlus

/-- Charged-kaon cutoff: the parent mass in `m_e` units. -/
def kaonFiniteCutoff : ℝ := CompositeMasses.kaonPlus

/-- Neutral-pion cutoff: the parent mass in `m_e` units. -/
def neutralPionFiniteCutoff : ℝ := CompositeMasses.pion0

theorem pionFiniteCutoff_gt_twelve : (12 : ℝ) < pionFiniteCutoff := by
  unfold pionFiniteCutoff
  linarith [LeptonMasses.pionPlus_value.1]

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
  exact PMElementaryParticles.NeutralPionWidth.neutralPionWidthE8_bounds

/-- Certified finite-channel neutral-pion lifetime enclosure. -/
theorem neutralPionFiniteLifetime_bounds :
    (6.56e4 : ℝ) < neutralPionFiniteLifetime ∧ neutralPionFiniteLifetime < (6.58e4 : ℝ) := by
  rw [neutralPionFiniteLifetime_eq_continuum]
  exact PMElementaryParticles.NeutralPionWidth.neutralPionLifetimeE8_bounds

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

end PMAtoms
