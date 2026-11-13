import PMHadrons.CompositeMasses

/-!
# Composite-mass measured pulls (moved from the PMElementaryParticles comparison leaf)

The E8 composite-mass formulas and their certified `*_value` enclosures stay in
`PMHadrons.CompositeMasses`; the CODATA/PDG pull comparisons live here.

`m_e c² = 0.51099895069` MeV and `ħc = 197.3269804` MeV·fm (CODATA 2022) are comparison units.
-/

noncomputable section
namespace E8PConstants.CompositeMassPulls
open PMSubstrate PMElementaryParticles PMHadrons.CompositeMasses

theorem proton_ratio : |(proton - 1836.152673426) / 0.000000032| < 1 := by
  have h := proton_value
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem neutron_ratio : |(neutron - 1838.68366200) / 0.00000074| < 0.2 := by
  have h := neutron_value
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem pion_mass : |(pion0 * me - 134.9768) / 0.0005| < 0.9 := by
  have hg := g_b
  unfold pion0 me PMSubstrate.SIUnits.electronMassMeV
  rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.nu_eq]
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith [hg.1]
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith [hg.2]

theorem kaon0_mass : |(kaon0 * me - 497.611) / 0.013| < 0.2 := by
  have hg := g_b; have hp := pi_b
  unfold kaon0 me PMSubstrate.SIUnits.electronMassMeV
  rw [PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.D_eq,
    PMSubstrate.E8Values.nu_eq]
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith [hg.1, hp.2]
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith [hg.2, hp.1]

/-- Direct two-sided enclosure of the charged kaon in `m_e` units. -/

theorem kaonPlus_mass : |(kaonPlus * me - 493.677) / 0.016| < 0.1 := by
  have hg := g_b; have hp := pi_b; have ha := a_b
  have hs : (0.7071067811 : ℝ) < 1 / Real.sqrt 2 ∧ 1 / Real.sqrt 2 < 0.7071067812 := by
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hpos := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
    constructor
    · rw [lt_div_iff₀ hpos]; nlinarith
    · rw [div_lt_iff₀ hpos]; nlinarith
  unfold kaonPlus me PMSubstrate.SIUnits.electronMassMeV
  rw [PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.D_eq]
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith [hg.1, hp.1, hs.2, ha.2]
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith [hg.2, hp.2, hs.1, ha.1]

theorem proton_radius : |(4 * hbarc / (proton * me) - 0.84075) / 0.00064| < 0.8 := by
  have h := proton_value
  have hpos : 0 < proton * me := by unfold me PMSubstrate.SIUnits.electronMassMeV; nlinarith
  have r1 : 4 * hbarc / (proton * me) < 0.841237 := by
    rw [div_lt_iff₀ hpos]; unfold hbarc PMSubstrate.SIUnits.hbarcMeVFm me PMSubstrate.SIUnits.electronMassMeV; nlinarith
  have r2 : 0.841235 < 4 * hbarc / (proton * me) := by
    rw [lt_div_iff₀ hpos]; unfold hbarc PMSubstrate.SIUnits.hbarcMeVFm me PMSubstrate.SIUnits.electronMassMeV; nlinarith
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-! ## The ledger counts are pinned by the data

Replace the proton's Toll count `5` and Margin divisor `χ = 2` by naturals `k`, `j`, and the
neutron's `3` and `1` likewise. One Toll is `1.19·10⁻⁵ m_e` and one Margin `2.9·10⁻⁶ m_e`, far larger
than the CODATA uncertainties, so the counts are fixed exactly.
* `proton_counts`: within `1σ` of CODATA exactly when `k = 5` and `j = 2`.
* `neutron_counts`: within `1σ` exactly when `k = 3` and `j = 1`.
These test the proposed counts (σ and σ − χ synchronized dimensions; boundary and volumetric Margin
shares); they do not derive why a baryon synchronizes those dimensions. -/


theorem proton_counts (k j : ℕ) (hj : 0 < j) :
    |(protonWith k j - 1836.152673426) / 0.000000032| < 1 ↔ k = 5 ∧ j = 2 := by
  have hv := proton_value
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have e : protonWith k j = proton + (k * zTol - zMar / j - (5 * zTol - zMar / 2)) := by
    unfold protonWith proton
    rw [PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq]
    ring
  constructor
  · intro h
    rw [abs_lt, lt_div_iff₀ (by norm_num), div_lt_iff₀ (by norm_num), e] at h
    obtain ⟨h1, h2⟩ := h
    rw [zTol_val, zMar_val] at h1 h2
    have hr0 : 0 < 1 / (343914 : ℝ) / j := by positivity
    have hr1 : 1 / (343914 : ℝ) / j ≤ 1 / 343914 := div_le_self (by norm_num) (by exact_mod_cast hj)
    have k1 : (4 : ℝ) < k := by nlinarith
    have k2 : (k : ℝ) < 6 := by nlinarith
    have hk : k = 5 := by
      have a : 4 < k := by exact_mod_cast k1
      have b : k < 6 := by exact_mod_cast k2
      omega
    subst hk
    have j1 : (1.9 : ℝ) < j := by
      by_contra hc; push Not at hc
      have : 1 / (343914 : ℝ) / 1.9 ≤ 1 / 343914 / j := by
        apply div_le_div_of_nonneg_left (by norm_num) hjR hc
      push_cast at h1 h2; nlinarith
    have j2 : (j : ℝ) < 2.1 := by
      by_contra hc; push Not at hc
      have : 1 / (343914 : ℝ) / j ≤ 1 / 343914 / 2.1 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      push_cast at h1 h2; nlinarith
    have a : 1 < j := by
      have : (1 : ℝ) < j := by linarith
      exact_mod_cast this
    have b : j < 3 := by
      have : (j : ℝ) < 3 := by linarith
      exact_mod_cast this
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, rfl⟩
    rw [e]; push_cast; ring_nf
    have := proton_ratio
    convert this using 3; ring

theorem neutron_counts (k j : ℕ) (hj : 0 < j) :
    |(neutronWith k j - 1838.68366200) / 0.00000074| < 1 ↔ k = 3 ∧ j = 1 := by
  have hv := neutron_value
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have e : neutronWith k j = neutron + (k * zTol - zMar / j - (3 * zTol - zMar)) := by
    unfold neutronWith neutron
    rw [PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq]
    ring
  constructor
  · intro h
    rw [abs_lt, lt_div_iff₀ (by norm_num), div_lt_iff₀ (by norm_num), e] at h
    obtain ⟨h1, h2⟩ := h
    rw [zTol_val, zMar_val] at h1 h2
    have hr0 : 0 < 1 / (343914 : ℝ) / j := by positivity
    have hr1 : 1 / (343914 : ℝ) / j ≤ 1 / 343914 := div_le_self (by norm_num) (by exact_mod_cast hj)
    have k1 : (2 : ℝ) < k := by nlinarith
    have k2 : (k : ℝ) < 4 := by nlinarith
    have hk : k = 3 := by
      have a : 2 < k := by exact_mod_cast k1
      have b : k < 4 := by exact_mod_cast k2
      omega
    subst hk
    have j2 : (j : ℝ) < 1.5 := by
      by_contra hc; push Not at hc
      have : 1 / (343914 : ℝ) / j ≤ 1 / 343914 / 1.5 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      push_cast at h1 h2; nlinarith
    have b : j < 2 := by
      have : (j : ℝ) < 2 := by linarith
      exact_mod_cast this
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, rfl⟩
    rw [e]; push_cast; ring_nf
    have := neutron_ratio
    rw [abs_lt] at this ⊢; constructor <;> linarith [this.1, this.2]


end E8PConstants.CompositeMassPulls
