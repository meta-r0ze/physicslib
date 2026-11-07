import PMElementaryParticles.MuonRate
import PMElementaryParticles.LeptonMasses
import PMElementaryParticles.NeutronRate
import PMElementaryParticles.Widths
import PMSubstrate.E8Values
import Mathlib.Tactic

/-! **Comparison / E8-input check.**

The muon width uses the E8-derived Fermi constant and E8 muon mass with the
continuum massless-pair phase space proved in `MuonRate`.

```
Γ_μ = G_F² m_μ⁵ / (192π³)
τ_μ = 1/Γ_μ
```

This is not a finite spectral-channel prediction; it is the E8-input continuum
check.
-/

noncomputable section
namespace PMElementaryParticles.MuonLifetime

open PMElementaryParticles.LeptonMasses
open PMElementaryParticles.NeutronRate
open PMElementaryParticles.Widths

/-- Muon width in `m_e` units. -/
def muonWidth : ℝ :=
  fermiME ^ 2 * muon ^ 5 / (192 * Real.pi ^ 3)

theorem muonWidth_eq_integral :
    muonWidth = ∫ E in (0 : ℝ)..(muon / 2), MuonRate.rate fermiME muon E := by
  unfold muonWidth
  rw [MuonRate.muon_rate]

theorem muonWidth_pos : 0 < muonWidth := by
  unfold muonWidth
  have hm : 0 < muon := by linarith [muon_value.1]
  have hnum : 0 < fermiME ^ 2 * muon ^ 5 :=
    mul_pos (sq_pos_of_pos fermiME_pos) (pow_pos hm 5)
  have hden : 0 < 192 * Real.pi ^ 3 := by positivity
  exact div_pos hnum hden

/-- Muon mean life in `m_e⁻¹` units. -/
def muonLifetime : ℝ := lifetime 1 muonWidth

theorem muonLifetime_eq : muonLifetime = 1 / muonWidth := rfl

theorem muonLifetime_pos : 0 < muonLifetime :=
  lifetime_pos (by norm_num) muonWidth_pos

/-- E8 coefficient `D(σ−χ)ν = 4·3·16 = 192`. -/
def muonCoefficientE8 : Nat :=
  PMSubstrate.E8Values.D * (PMSubstrate.E8Values.sigma - PMSubstrate.E8Values.chi) *
    PMSubstrate.E8Values.nu

theorem muonCoefficientE8_eq : muonCoefficientE8 = 192 := by
  unfold muonCoefficientE8
  norm_num [PMSubstrate.E8Values.D, PMSubstrate.E8Values.sigma,
    PMSubstrate.E8Values.chi, PMSubstrate.E8Values.nu, PMSubstrate.baseline]

/-- Muon width written with the E8 coefficient. -/
theorem muonWidth_eq_E8 :
    muonWidth =
      fermiME ^ 2 * muon ^ 5 / ((muonCoefficientE8 : ℝ) * Real.pi ^ 3) := by
  unfold muonWidth
  rw [muonCoefficientE8_eq]
  norm_num


/-- Broad enclosure of the Fermi constant in `m_e⁻²`. -/
theorem fermiME_bounds : (2.9e-12 : ℝ) < fermiME ∧ fermiME < (3.2e-12 : ℝ) := by
  have h := PMConstants.ElectroweakBounds.fermi_bounds
  have he : (2.6e-7 : ℝ) < PMConstants.ElectroweakBounds.electronGeV ^ 2 ∧
      PMConstants.ElectroweakBounds.electronGeV ^ 2 < (2.62e-7 : ℝ) := by
    unfold PMConstants.ElectroweakBounds.electronGeV; norm_num
  unfold fermiME
  change (2.9e-12 : ℝ) <
    PMConstants.ElectroweakE8.fermi PMConstants.CertifiedConstants.α
      PMConstants.ElectroweakBounds.electronGeV *
    PMConstants.ElectroweakBounds.electronGeV ^ 2 ∧
    PMConstants.ElectroweakE8.fermi PMConstants.CertifiedConstants.α
      PMConstants.ElectroweakBounds.electronGeV *
    PMConstants.ElectroweakBounds.electronGeV ^ 2 < (3.2e-12 : ℝ)
  constructor <;> nlinarith [h.1, h.2, he.1, he.2]

/-- Tighter enclosure of the Fermi constant in `m_e⁻²`. -/
theorem fermiME_bounds_tight : (3.04e-12 : ℝ) < fermiME ∧ fermiME < (3.05e-12 : ℝ) := by
  have h := PMConstants.ElectroweakBounds.fermi_bounds
  have he : (2.6111e-7 : ℝ) < PMConstants.ElectroweakBounds.electronGeV ^ 2 ∧
      PMConstants.ElectroweakBounds.electronGeV ^ 2 < (2.6113e-7 : ℝ) := by
    unfold PMConstants.ElectroweakBounds.electronGeV; norm_num
  unfold fermiME
  change (3.04e-12 : ℝ) <
    PMConstants.ElectroweakE8.fermi PMConstants.CertifiedConstants.α
      PMConstants.ElectroweakBounds.electronGeV *
    PMConstants.ElectroweakBounds.electronGeV ^ 2 ∧
    PMConstants.ElectroweakE8.fermi PMConstants.CertifiedConstants.α
      PMConstants.ElectroweakBounds.electronGeV *
    PMConstants.ElectroweakBounds.electronGeV ^ 2 < (3.05e-12 : ℝ)
  constructor <;> nlinarith [h.1, h.2, he.1, he.2]

/-- Broad enclosure of the muon width in `m_e` units. -/
theorem muonWidth_bounds : (4.0e-16 : ℝ) < muonWidth ∧ muonWidth < 8.0e-16 := by
  have hf := fermiME_bounds
  have hm1 : (200.0 : ℝ) < muon := by linarith [muon_value.1]
  have hm2 : muon < (210.0 : ℝ) := by linarith [muon_value.2]
  have hp1 : (3.14 : ℝ) < Real.pi := by linarith [Real.pi_gt_d20]
  have hp2 : Real.pi < (3.15 : ℝ) := by linarith [Real.pi_lt_d20]
  have hf2lo : (8e-24 : ℝ) < fermiME ^ 2 := by nlinarith [hf.1]
  have hf2hi : fermiME ^ 2 < (1.1e-23 : ℝ) := by nlinarith [hf.2]
  have hm5lo : (3.2e11 : ℝ) < muon ^ 5 := by
    have h := pow_lt_pow_left₀ hm1 (by linarith [hm1] : (0:ℝ) ≤ (200.0:ℝ))
      (by norm_num : (5:ℕ) ≠ 0)
    norm_num at h; linarith [h]
  have hm5hi : muon ^ 5 < (4.1e11 : ℝ) := by
    have h := pow_lt_pow_left₀ hm2 (by linarith [hm1] : (0:ℝ) ≤ muon)
      (by norm_num : (5:ℕ) ≠ 0)
    norm_num at h; linarith [h]
  have hp3lo : (30 : ℝ) < Real.pi ^ 3 := by
    have h := pow_lt_pow_left₀ hp1 (by linarith [hp1] : (0:ℝ) ≤ (3.14:ℝ))
      (by norm_num : (3:ℕ) ≠ 0)
    norm_num at h; linarith [h]
  have hp3hi : Real.pi ^ 3 < (32 : ℝ) := by
    have h := pow_lt_pow_left₀ hp2 (by linarith [hp1] : (0:ℝ) ≤ Real.pi)
      (by norm_num : (3:ℕ) ≠ 0)
    norm_num at h; linarith [h]
  have hf2pos : (0 : ℝ) < fermiME ^ 2 := by positivity
  have hm5pos : (0 : ℝ) < muon ^ 5 := by positivity
  have hnumlo : (8e-24 : ℝ) * (3.2e11 : ℝ) < fermiME ^ 2 * muon ^ 5 :=
    mul_lt_mul hf2lo hm5lo.le (by norm_num) (le_of_lt hf2pos)
  have hnumhi : fermiME ^ 2 * muon ^ 5 < (1.1e-23 : ℝ) * (4.1e11 : ℝ) :=
    mul_lt_mul hf2hi hm5hi.le hm5pos (by norm_num)
  have hden : (0 : ℝ) < 192 * Real.pi ^ 3 := by positivity
  unfold muonWidth
  constructor
  · rw [lt_div_iff₀ hden]; nlinarith [hnumlo, hp3hi]
  · rw [div_lt_iff₀ hden]; nlinarith [hnumhi, hp3lo]

/-- Broad enclosure of the muon lifetime in `m_e⁻¹` natural units. -/
theorem muonLifetime_bounds :
    (1.25e15 : ℝ) < muonLifetime ∧ muonLifetime < 2.5e15 := by
  have hw := muonWidth_bounds
  have hpos : 0 < muonWidth := lt_trans (by norm_num) hw.1
  unfold muonLifetime PMElementaryParticles.Widths.lifetime
  constructor
  · rw [lt_div_iff₀ hpos]; nlinarith [hw.2]
  · rw [div_lt_iff₀ hpos]; nlinarith [hw.1]

end PMElementaryParticles.MuonLifetime
