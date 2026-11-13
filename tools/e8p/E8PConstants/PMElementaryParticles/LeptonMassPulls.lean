import PMHadrons.MesonMasses
import PMHadrons.CompositeMasses
import PMElementaryParticles.LeptonMasses

/-!
# Charged-lepton / pion measured pulls (moved from the PMElementaryParticles leaf)

The E8 lepton and pion formulas and their E8-only enclosures stay in
`PMElementaryParticles.LeptonMasses`; the CODATA 2022 / PDG measured comparisons
live here. No measured number enters a theorem statement used by the derivation.
-/

noncomputable section
namespace E8PConstants.LeptonMassPulls
open PMElementaryParticles.LeptonMasses
open PMHadrons.MesonMasses
open PMHadrons.CompositeMasses

theorem muon_tension : -2.5 < (muon - 206.7682827) / 0.0000046 ∧
    (muon - 206.7682827) / 0.0000046 < -2.3 := by
  have h := muon_value
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem tau_tension : -2.1 < (tau * me - 1776.93) / 0.09 ∧ (tau * me - 1776.93) / 0.09 < -2.0 := by
  rw [tau_value]; unfold me PMSubstrate.SIUnits.electronMassMeV; constructor <;> norm_num

theorem pionPlus_mass : |(pionPlus * me - 139.57039) / 0.00018| < 0.2 := by
  have hg := g_b; have ha := a_b
  rw [pionPlus_ledger]
  rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.D_eq]
  unfold me PMSubstrate.SIUnits.electronMassMeV
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith [hg.1, ha.2]
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith [hg.2, ha.1]

/-! ## Mass splittings (measured comparisons)

* `kaon_inversion`: `m_K⁰ − m_K⁺` in `(3.93, 3.94)` MeV (PDG `497.611 − 493.677 = 3.934`).
* `pion_splitting`: `m_π⁺ − m_π⁰` in `(4.5933, 4.5935)` MeV (PDG `4.5936(5)`, within `0.6σ`).
-/

theorem kaon_inversion : 3.93 < (kaon0 - kaonPlus) * me ∧ (kaon0 - kaonPlus) * me < 3.94 := by
  have hp := pi_b; have ha := a_b
  have hs : (0.7071067811 : ℝ) < 1 / Real.sqrt 2 ∧ 1 / Real.sqrt 2 < 0.7071067812 := by
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hpos := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
    constructor
    · rw [lt_div_iff₀ hpos]; nlinarith
    · rw [div_lt_iff₀ hpos]; nlinarith
  unfold kaon0 kaonPlus me PMSubstrate.SIUnits.electronMassMeV
  rw [PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq,
    PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.nu_eq]
  constructor <;> nlinarith [hp.1, hp.2, hs.1, hs.2, ha.1, ha.2]

theorem pion_splitting : 4.5933 < (pionPlus - pion0) * me ∧ (pionPlus - pion0) * me < 4.5935 := by
  have ha := a_b
  rw [pionPlus_ledger]
  unfold pion0 me PMSubstrate.SIUnits.electronMassMeV
  rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.D_eq]
  constructor <;> nlinarith [ha.1, ha.2]

end E8PConstants.LeptonMassPulls
