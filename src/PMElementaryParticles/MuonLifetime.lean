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

end PMElementaryParticles.MuonLifetime
