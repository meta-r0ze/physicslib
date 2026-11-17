import PMHadrons.MesonFiniteChannels
import PMHadrons.KaonPionRatio
import PMFlavor.Values

/-!
# One charged-current normalization for the meson rates

Counting each factor once, the inclusive muonic width of a charged meson is

  `Γ(P → μν(γ)) = G_F² |q V|² f_P² m_P m_μ² (1 − m_μ²/m_P²)² / (8π) · (1 + δ_P)`,

* `G_F` from muon decay (E8, `PMElementaryParticles.SharedUnits.fermiME`);
* `q² = 515/516`, PMFlavor's dressing of colour-carrier transitions, which muon decay does not carry
  (`PMFlavor.DressingInheritance`, `PMFlavor.Values.q2`);
* `|V|` the E8 CKM entry (`PMFlavor.Values.vud`; `KaonWidth.vusE8`, already inside `kaonWidthE8`);
* `δ_P` the full radiative correction, short plus long distance with hadronic structure,
  **supplied**: `δ_π = 0.0176(21)`, `δ_K = 0.0107(21)` (PDG review, Rosner, Stone and Van de Water,
  arXiv:1509.02220). Its short-distance part is the derived running
  (`ShortDistanceRunning.runningFactor_bounds`, `R − 1 = 0.0212` at `μ = m_p`).

This replaces the pion-channel factor `32/33` (`E8Margin.pionMargin`) and `DecayInstantiation`'s
`sharedFactor`, which stood in for `|V_ud|²(1 + δ_π)` and fitted the pion by construction. In this
convention the residuals are the emission counts behind `f_π` (`1890`) and `f_K` (`1593`):
`tools/charged_current_normalization.py`, PMHadrons REVIEW.

* `pionMuLifetimeSeconds_bounds`: `2.61592–2.61602 × 10⁻⁸ s` (measured `τ_π/BR(μν(γ)) = 2.60362`).
* `kaonMuLifetimeSeconds_bounds`: `1.99692–1.99700 × 10⁻⁸ s` (measured `1.94777`).
* `kaonPionRatioRadiative_bounds`: `Γ_K/Γ_π` with `(1 + δ_K)/(1 + δ_π)`: `1.309978–1.309980`
  (measured `1.33672`); the dressing cancels in the ratio.
-/

noncomputable section
namespace PMHadrons.ChargedCurrentRate

open PMElementaryParticles

/-- Supplied full radiative corrections (arXiv:1509.02220). -/
def deltaPi : ℝ := 0.0176
def deltaK : ℝ := 0.0107

/-- The tree-level E8 pion lifetime in seconds, with no CKM or radiative factor. -/
def pionBaseSeconds : ℝ := PionWidth.pionLifetimeE8 * PhysicalUnits.electronTime

def pionMuLifetimeSeconds : ℝ :=
  pionBaseSeconds / (PMFlavor.Values.q2 * PMFlavor.Values.vud ^ 2 * (1 + deltaPi))

/-- The kaon carries `|V_us|²` inside `kaonWidthE8`. -/
def kaonMuLifetimeSeconds : ℝ :=
  KaonWidth.kaonLifetimeE8 * PhysicalUnits.electronTime / (PMFlavor.Values.q2 * (1 + deltaK))

def kaonPionRatioRadiative : ℝ := KaonPionRatio.kaonPionWidthRatio * ((1 + deltaK) / (1 + deltaPi))

lemma pionBase_eq : pionBaseSeconds = PMSubstrate.E8Margin.pionMargin * pionLifetimeCorrectedSeconds := by
  have hm : PMSubstrate.E8Margin.pionMargin ≠ 0 := by
    rw [PMSubstrate.E8Margin.pionMargin_eq]; norm_num
  unfold pionBaseSeconds pionLifetimeCorrectedSeconds PMSubstrate.E8Margin.pionCorrectedLifetime
  field_simp

theorem pionBase_bounds : (2.52303515e-8 : ℝ) < pionBaseSeconds ∧ pionBaseSeconds < 2.52307394e-8 := by
  rw [pionBase_eq, PMSubstrate.E8Margin.pionMargin_eq]
  have h := pionLifetimeCorrectedSeconds_bounds
  constructor <;> nlinarith [h.1, h.2]

lemma vud_sq_bounds : (0.974490 : ℝ) ^ 2 < PMFlavor.Values.vud ^ 2 ∧
    PMFlavor.Values.vud ^ 2 < (0.974499 : ℝ) ^ 2 := by
  have h := PMFlavor.Values.vud_bounds
  exact ⟨pow_lt_pow_left₀ h.1 (by norm_num) (by norm_num),
    pow_lt_pow_left₀ h.2 (by linarith [h.1]) (by norm_num)⟩

theorem pionMuLifetimeSeconds_bounds :
    (2.61592e-8 : ℝ) < pionMuLifetimeSeconds ∧ pionMuLifetimeSeconds < 2.61602e-8 := by
  obtain ⟨b1, b2⟩ := pionBase_bounds
  obtain ⟨v1, v2⟩ := vud_sq_bounds
  have hq : PMFlavor.Values.q2 = 515 / 516 := PMFlavor.Values.q2_eq
  unfold pionMuLifetimeSeconds deltaPi
  rw [hq]
  set V := PMFlavor.Values.vud ^ 2
  have hD : 0 < 515 / 516 * V * (1 + 0.0176 : ℝ) := by nlinarith
  constructor
  · rw [lt_div_iff₀ hD]; nlinarith
  · rw [div_lt_iff₀ hD]; nlinarith

lemma kaonLifetime_eq : KaonWidth.kaonLifetimeE8 * PhysicalUnits.electronTime =
    pionBaseSeconds / (PMFlavor.Values.vud ^ 2 * KaonPionRatio.kaonPionWidthRatio) := by
  have hv : PMFlavor.Values.vud ^ 2 ≠ 0 := by
    have h := PMFlavor.Values.vud_bounds
    exact pow_ne_zero 2 (by intro h0; rw [h0] at h; norm_num at h)
  have hp : PionWidth.pionWidthE8 ≠ 0 := by
    have h := PionWidth.pionWidthE8_bounds; intro h0; rw [h0] at h; norm_num at h
  have hk : KaonWidth.kaonWidthE8 ≠ 0 := by
    have h := KaonWidth.kaonWidthE8_bounds; intro h0; rw [h0] at h; norm_num at h
  have e1 : KaonWidth.kaonLifetimeE8 = 1 / KaonWidth.kaonWidthE8 := rfl
  have e2 : pionBaseSeconds = 1 / PionWidth.pionWidthE8 * PhysicalUnits.electronTime := rfl
  have e3 : KaonPionRatio.kaonPionWidthRatio =
      KaonWidth.kaonWidthE8 / (PionWidth.pionWidthE8 * PMFlavor.Values.vud ^ 2) := rfl
  rw [e1, e2, e3]
  generalize KaonWidth.kaonWidthE8 = k at hk ⊢
  generalize PionWidth.pionWidthE8 = w at hp ⊢
  generalize PMFlavor.Values.vud ^ 2 = V at hv ⊢
  field_simp

theorem kaonMuLifetimeSeconds_bounds :
    (1.99692e-8 : ℝ) < kaonMuLifetimeSeconds ∧ kaonMuLifetimeSeconds < 1.99700e-8 := by
  obtain ⟨b1, b2⟩ := pionBase_bounds
  obtain ⟨v1, v2⟩ := vud_sq_bounds
  obtain ⟨r1, r2⟩ := KaonPionRatio.kaonPionWidthRatio_bounds
  have hq : PMFlavor.Values.q2 = 515 / 516 := PMFlavor.Values.q2_eq
  unfold kaonMuLifetimeSeconds deltaK
  rw [kaonLifetime_eq, hq, div_div]
  set V := PMFlavor.Values.vud ^ 2
  set Rr := KaonPionRatio.kaonPionWidthRatio
  have hVR1 : (0.974490 : ℝ) ^ 2 * 1.318922 < V * Rr := mul_lt_mul'' v1 r1 (by norm_num) (by norm_num)
  have hVR2 : V * Rr < (0.974499 : ℝ) ^ 2 * 1.318923 := mul_lt_mul'' v2 r2 (by nlinarith) (by linarith)
  have hD : 0 < V * Rr * (515 / 516 * (1 + 0.0107 : ℝ)) := by nlinarith
  constructor
  · rw [lt_div_iff₀ hD]; nlinarith
  · rw [div_lt_iff₀ hD]; nlinarith

theorem kaonPionRatioRadiative_bounds :
    (1.309978 : ℝ) < kaonPionRatioRadiative ∧ kaonPionRatioRadiative < 1.309980 := by
  obtain ⟨r1, r2⟩ := KaonPionRatio.kaonPionWidthRatio_bounds
  unfold kaonPionRatioRadiative deltaK deltaPi
  constructor <;> nlinarith

end PMHadrons.ChargedCurrentRate
