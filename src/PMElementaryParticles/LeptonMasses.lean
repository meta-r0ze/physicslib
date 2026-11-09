import PMElementaryParticles.CompositeMasses

/-!

# Charged lepton and charged pion masses

Units of `m_e`; `α`, `α⁻¹`, `π` as in `CompositeMasses`.

| Formula | E8 value |
| --- | --- |
| `m_μ = Δσ − χ − 2π + α(χ+σ)/(1−α)` | `206.7682717` |
| `m_τ = Δ²χ − Δσ − χ − D` | `3477`, i.e. `1776.743` MeV |
| `m_π⁺ = 2α⁻¹ − σχ + 1/(ν−χ) + σ + D − α(σ−χ)/χ` | `139.57041` MeV |

This module keeps only the E8 formulas and their **E8-only** enclosures. The
measured CODATA/PDG comparisons (`muon_tension`, `tau_tension`, `pionPlus_mass`,
`kaon_inversion`, `pion_splitting`) live in
`tools/e8p/E8PConstants/LeptonMassPulls.lean`.
-/

noncomputable section
namespace PMElementaryParticles.LeptonMasses
open PMElementaryParticles.CompositeMasses

def muon : ℝ := 43 * 5 - 2 - 2 * Real.pi + αe * (2 + 5) / (1 - αe)
def tau : ℝ := 43 ^ 2 * 2 - 43 * 5 - 2 - 4
def pionPlus : ℝ := 2 * αinv - 5 * 2 + 1 / (16 - 2) + 5 + 4 - αe * ((5 - 2) / 2)

theorem muon_value : 206.7682716 < muon ∧ muon < 206.7682718 := by
  have hp := pi_b; have ha := a_b
  have h1 : 0 < 1 - αe := by linarith [ha.2]
  have q1 : αe * 7 / (1 - αe) < 0.05145697 := by
    rw [div_lt_iff₀ h1]; nlinarith [ha.1, ha.2]
  have q2 : 0.05145696 < αe * 7 / (1 - αe) := by
    rw [lt_div_iff₀ h1]; nlinarith [ha.1, ha.2]
  unfold muon
  have e : αe * (2 + 5) / (1 - αe) = αe * 7 / (1 - αe) := by norm_num
  rw [e]; constructor <;> nlinarith [hp.1, hp.2]

theorem tau_value : tau = 3477 := by norm_num [tau]

/-- A direct two-sided enclosure of the charged pion in `m_e` units. -/
theorem pionPlus_value : (273.1 : ℝ) < pionPlus ∧ pionPlus < 273.2 := by
  have hg := g_b; have ha := a_b
  unfold pionPlus
  constructor <;> nlinarith [hg.1, hg.2, ha.1, ha.2]

/-- The charged-pion mass in MeV, as an E8-only enclosure (no measured reference). -/
theorem pionPlus_mev_value : (139.570354 : ℝ) < pionPlus * me ∧ pionPlus * me < 139.570426 := by
  have hg := g_b; have ha := a_b
  unfold pionPlus me
  constructor <;> nlinarith [hg.1, hg.2, ha.1, ha.2]

end PMElementaryParticles.LeptonMasses
