import PMHadrons.PionWidth
import PMHadrons.KaonWidth
import PMHadrons.MesonMasses
import PMFlavor.Values
import Mathlib.Tactic

/-! **Comparison / structural.**

# `Γ(K→μν)/Γ(π→μν)` with the CKM factor on both widths

The kaon width carries `|V_us|²` (`KaonWidth.kaonWidthE8`). The same two-body formula for the
pion carries `|V_ud|²`; `PionWidth.pionWidthE8` leaves it out and the pion-channel margin
`32/33` stands in for it. In the ratio, `G_F`, `m_μ²`, `8π` and any correction common to the
two channels cancel, so no margin enters:

  `Γ_K/Γ_π = (|V_us|/|V_ud|)² (f_K/f_π)² (m_K/m_π) F_K/F_π`,  `F = (1 − m_μ²/m²)²`.

On E8, `|V_us|/|V_ud| = s₁₂/c₁₂` (`c₁₃` cancels) with `s₁₂ = π/14`, and
`f_K/f_π = 1890/1593 = 70/59` exactly (both are `v` over a count). The ratio is
`1.318922…`; without `|V_ud|²` on the pion it would be `6%` lower again.
-/

noncomputable section
namespace PMHadrons.KaonPionRatio
open PMElementaryParticles

/-- `Γ(K⁺→μ⁺ν)/Γ(π⁺→μ⁺ν)` with `|V_us|²` on the kaon and `|V_ud|²` on the pion. -/
def kaonPionWidthRatio : ℝ :=
  KaonWidth.kaonWidthE8 / (PionWidth.pionWidthE8 * PMFlavor.Values.vud ^ 2)

/-- `(1 − (m/M)²)²` between the bounds given by `r₁ M < m < r₂ M`. -/
lemma phase_bounds {m M r1 r2 lo hi : ℝ} (hM : 0 < M) (hm1 : r1 * M < m) (hm2 : m < r2 * M)
    (hr1 : 0 ≤ r1) (hr2 : r2 ^ 2 < 1) (hlo : lo < (1 - r2 ^ 2) ^ 2) (hhi : (1 - r1 ^ 2) ^ 2 < hi) :
    lo < (1 - (m / M) ^ 2) ^ 2 ∧ (1 - (m / M) ^ 2) ^ 2 < hi := by
  have h1 : r1 < m / M := by rw [lt_div_iff₀ hM]; linarith
  have h2 : m / M < r2 := by rw [div_lt_iff₀ hM]; linarith
  have h0 : 0 ≤ m / M := le_of_lt (lt_of_le_of_lt hr1 h1)
  have hq1 : r1 ^ 2 < (m / M) ^ 2 := pow_lt_pow_left₀ h1 hr1 two_ne_zero
  have hq2 : (m / M) ^ 2 < r2 ^ 2 := pow_lt_pow_left₀ h2 h0 two_ne_zero
  have a1 : 1 - r2 ^ 2 < 1 - (m / M) ^ 2 := by linarith
  have a2 : 1 - (m / M) ^ 2 < 1 - r1 ^ 2 := by linarith
  have b1 := pow_lt_pow_left₀ a1 (by linarith) two_ne_zero
  have b2 := pow_lt_pow_left₀ a2 (by linarith) two_ne_zero
  exact ⟨by linarith, by linarith⟩

lemma meson_masses :
    (966.10031 : ℝ) < CompositeMasses.kaonPlus ∧ CompositeMasses.kaonPlus < 966.10032 ∧
    (273.13248 : ℝ) < MesonMasses.pionPlus ∧ MesonMasses.pionPlus < 273.132483 := by
  have hK := CompositeMasses.kaonPlus_mev_value
  have hP := MesonMasses.pionPlus_mev_value
  simp only [PMElementaryParticles.SharedUnits.me, PMSubstrate.SIUnits.electronMassMeV] at hK hP
  exact ⟨by linarith [hK.1], by linarith [hK.2], by linarith [hP.1], by linarith [hP.2]⟩

lemma kaon_phase :
    (0.910485988 : ℝ) <
      (1 - (LeptonMasses.muon / CompositeMasses.kaonPlus) ^ 2) ^ 2 ∧
    (1 - (LeptonMasses.muon / CompositeMasses.kaonPlus) ^ 2) ^ 2 < 0.910485997 := by
  obtain ⟨k1, k2, -, -⟩ := meson_masses
  have hm := LeptonMasses.muon_value
  exact phase_bounds (r1 := 0.21402360) (r2 := 0.21402361) (by linarith) (by linarith)
    (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma pion_phase :
    (0.182254087 : ℝ) <
      (1 - (LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 ∧
    (1 - (LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 < 0.182254114 := by
  obtain ⟨-, -, p1, p2⟩ := meson_masses
  have hm := LeptonMasses.muon_value
  exact phase_bounds (r1 := 0.75702556) (r2 := 0.75702558) (by linarith) (by linarith)
    (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `f_K/f_π = 1890/1593`: both decay constants are `v` over a count. -/
lemma decay_constants :
    KaonWidth.kaonDecayConstantE8 = PMConstants.Values.vev 1 / 1593 ∧
    PionWidth.pionDecayConstantE8 = PMConstants.Values.vev 1 / 1890 := by
  constructor
  · unfold KaonWidth.kaonDecayConstantE8
    rw [show (((PMSubstrate.E8Values.Delta : ℝ) ^ 2 -
        (PMSubstrate.E8Values.nu : ℝ) ^ 2)) = 1593 by
      norm_num [PMSubstrate.E8Values.Delta, PMSubstrate.E8Values.nu]]
  · unfold PionWidth.pionDecayConstantE8
    rw [show (((PMSubstrate.E8Values.Delta : ℝ) ^ 2 +
        ((PMSubstrate.E8Values.Delta - PMSubstrate.E8Values.chi : Nat) : ℝ))) = 1890 by
      norm_num [PMSubstrate.E8Values.Delta, PMSubstrate.E8Values.chi]]

/-- The ratio in closed form. -/
theorem kaonPionWidthRatio_eq :
    kaonPionWidthRatio =
      (PMFlavor.CKM.s12 / PMFlavor.CKM.c12) ^ 2 * (1890 / 1593) ^ 2 *
        (CompositeMasses.kaonPlus / MesonMasses.pionPlus) *
        ((1 - (LeptonMasses.muon / CompositeMasses.kaonPlus) ^ 2) ^ 2 /
          (1 - (LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2) := by
  obtain ⟨hk, hp⟩ := decay_constants
  have hf := PionWidth.pionDecayConstantE8_bounds
  have hV : PMConstants.Values.vev 1 ≠ 0 := by
    intro h0; rw [hp, h0] at hf; norm_num at hf
  obtain ⟨k1, -, p1, -⟩ := meson_masses
  have hKne : CompositeMasses.kaonPlus ≠ 0 := by intro h; rw [h] at k1; norm_num at k1
  have hPne : MesonMasses.pionPlus ≠ 0 := by intro h; rw [h] at p1; norm_num at p1
  have hmune : LeptonMasses.muon ≠ 0 := by
    have := LeptonMasses.muon_value.1; intro h; rw [h] at this; norm_num at this
  have hGne : PMElementaryParticles.SharedUnits.fermiME ≠ 0 :=
    PMElementaryParticles.SharedUnits.fermiME_pos.ne'
  have hc12 : PMFlavor.CKM.c12 ≠ 0 := PMFlavor.Values.c12_pos.ne'
  have hc13 : PMFlavor.CKM.c13 ≠ 0 := PMFlavor.Values.c13_pos.ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hFK : (1 - (LeptonMasses.muon / CompositeMasses.kaonPlus) ^ 2) ^ 2 ≠ 0 := by
    have := kaon_phase.1; intro h; rw [h] at this; norm_num at this
  have hFP : (1 - (LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 ≠ 0 := by
    have := pion_phase.1; intro h; rw [h] at this; norm_num at this
  unfold kaonPionWidthRatio PMFlavor.Values.vud KaonWidth.kaonWidthE8 KaonWidth.kaonWidthCKM
    KaonWidth.kaonWidth KaonWidth.vusE8 PMFlavor.Values.vus PionWidth.pionWidthE8 PionWidth.pionWidth
  rw [hk, hp]
  generalize (1 - (LeptonMasses.muon / CompositeMasses.kaonPlus) ^ 2) ^ 2 = A at hFK ⊢
  generalize (1 - (LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 = B at hFP ⊢
  field_simp

/-- **E8 `Γ(K→μν)/Γ(π→μν)` is between `1.318922` and `1.318923`.** -/
theorem kaonPionWidthRatio_bounds :
    (1.318922 : ℝ) < kaonPionWidthRatio ∧ kaonPionWidthRatio < 1.318923 := by
  rw [kaonPionWidthRatio_eq]
  -- `(s₁₂/c₁₂)² = s₁₂²/(1 − s₁₂²)`, `s₁₂² = π²/196`
  have hp1 : (3.14159265358979 : ℝ) < Real.pi := by linarith [Real.pi_gt_d20]
  have hp2 : Real.pi < (3.14159265358980 : ℝ) := by linarith [Real.pi_lt_d20]
  have hu : PMFlavor.CKM.s12 ^ 2 = Real.pi ^ 2 / 196 := by unfold PMFlavor.CKM.s12; ring
  have hq1 : (9.869604401089 : ℝ) < Real.pi ^ 2 := by nlinarith
  have hq2 : Real.pi ^ 2 < (9.869604401090 : ℝ) := by nlinarith
  have hu1 : (9.869604401089 / 196 : ℝ) < PMFlavor.CKM.s12 ^ 2 := by rw [hu]; linarith
  have hu2 : PMFlavor.CKM.s12 ^ 2 < (9.869604401090 / 196 : ℝ) := by rw [hu]; linarith
  have hupos : 0 < 1 - PMFlavor.CKM.s12 ^ 2 := by linarith
  have hT : (PMFlavor.CKM.s12 / PMFlavor.CKM.c12) ^ 2 =
      PMFlavor.CKM.s12 ^ 2 / (1 - PMFlavor.CKM.s12 ^ 2) := by
    rw [div_pow, show PMFlavor.CKM.c12 ^ 2 = 1 - PMFlavor.CKM.s12 ^ 2 by
      linarith [PMFlavor.Values.c12_pyth]]
  have hT1 : (0.05302521584038 : ℝ) < (PMFlavor.CKM.s12 / PMFlavor.CKM.c12) ^ 2 := by
    rw [hT, lt_div_iff₀ hupos]; linarith
  have hT2 : (PMFlavor.CKM.s12 / PMFlavor.CKM.c12) ^ 2 < (0.05302521584040 : ℝ) := by
    rw [hT, div_lt_iff₀ hupos]; linarith
  -- mass ratio
  obtain ⟨k1, k2, p1, p2⟩ := meson_masses
  have hPpos : (0 : ℝ) < MesonMasses.pionPlus := by linarith
  have hM1 : (966.10031 / 273.132483 : ℝ) < CompositeMasses.kaonPlus / MesonMasses.pionPlus := by
    rw [div_lt_div_iff₀ (by norm_num) hPpos]; nlinarith
  have hM2 : CompositeMasses.kaonPlus / MesonMasses.pionPlus < (966.10032 / 273.13248 : ℝ) := by
    rw [div_lt_div_iff₀ hPpos (by norm_num)]; nlinarith
  -- phase-space ratio
  obtain ⟨fk1, fk2⟩ := kaon_phase
  obtain ⟨fp1, fp2⟩ := pion_phase
  have hFPpos : (0 : ℝ) < (1 - (LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 := by linarith
  have hQ1 : (0.910485988 / 0.182254114 : ℝ) <
      (1 - (LeptonMasses.muon / CompositeMasses.kaonPlus) ^ 2) ^ 2 /
        (1 - (LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 := by
    rw [div_lt_div_iff₀ (by norm_num) hFPpos]; nlinarith
  have hQ2 : (1 - (LeptonMasses.muon / CompositeMasses.kaonPlus) ^ 2) ^ 2 /
        (1 - (LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 <
      (0.910485997 / 0.182254087 : ℝ) := by
    rw [div_lt_div_iff₀ hFPpos (by norm_num)]; nlinarith
  -- assemble
  have hTpos : (0 : ℝ) < (PMFlavor.CKM.s12 / PMFlavor.CKM.c12) ^ 2 := by linarith
  have hMpos : (0 : ℝ) < CompositeMasses.kaonPlus / MesonMasses.pionPlus := by
    linarith [show (0 : ℝ) < 966.10031 / 273.132483 by norm_num]
  have hQpos : (0 : ℝ) < (1 - (LeptonMasses.muon / CompositeMasses.kaonPlus) ^ 2) ^ 2 /
      (1 - (LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 := by
    linarith [show (0 : ℝ) < 0.910485988 / 0.182254114 by norm_num]
  have l1 := mul_lt_mul'' hT1 hM1 (by norm_num) (by norm_num)
  have l2 := mul_lt_mul'' l1 hQ1 (by norm_num) (by norm_num)
  have u1 := mul_lt_mul'' hT2 hM2 hTpos.le hMpos.le
  have u2 := mul_lt_mul'' u1 hQ2 (mul_pos hTpos hMpos).le hQpos.le
  have nlo : (1.318922 : ℝ) < (1890 / 1593) ^ 2 *
      ((0.05302521584038 : ℝ) * (966.10031 / 273.132483) * (0.910485988 / 0.182254114)) := by
    norm_num
  have nhi : (1890 / 1593 : ℝ) ^ 2 *
      ((0.05302521584040 : ℝ) * (966.10032 / 273.13248) * (0.910485997 / 0.182254087)) <
        1.318923 := by
    norm_num
  constructor <;> nlinarith [l2, u2, nlo, nhi]

end PMHadrons.KaonPionRatio
