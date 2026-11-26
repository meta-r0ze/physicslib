import PMElementaryParticles.TauLifetime
import PMElementaryParticles.MuonQEDLoops
import PMConstants.ElectroweakBounds

/-!
# The tau lifetime from the muon's, with the partial-width ratio corrected

`TauLifetime.tauLife` scales the measured muon lifetime by `(m_μ/m_τ)⁵` and the supplied
`B_e = Γ(τ → eνν̄)/Γ_τ`. The ratio of the two electronic partial widths has three further factors
(Marciano–Sirlin; PDG 2024, Eq. 10.10):

  `Γ(τ → eνν̄)/Γ(μ → eνν̄) = (m_τ/m_μ)⁵ · [f(x_τ)/f(x_μ)] · [r_W(m_τ)/r_W(m_μ)] · [δ_γ(m_τ)/δ_γ(m_μ)]`,

* `f`, the massive-electron phase space (`MassiveWidth.phase`, derived), at `x = (m_e/m_ℓ)²`;
* `r_W(m) = 1 + 3m²/(5M_W²)`, the `W` propagator, with the E8 `M_W` (`PMConstants.ElectroweakBounds`;
  its offset from the measured `M_W` moves the lifetime by `10⁻⁵`);
* `δ_γ(m) = 1 − (α(m)/π)(π²/2 − 25/8)`, the one-loop QED factor at each lepton's scale:
  `α(m_μ)` from E8 `α` (`MuonQEDLoops.alphaR`), `α(m_τ)⁻¹ = 133.3` supplied (it includes
  hadronic vacuum polarization).

`tauLifeCorrected = tauLife · [f(x_μ)/f(x_τ)] · [r_W(m_μ)/r_W(m_τ)] · [δ_γ(m_μ)/δ_γ(m_τ)]`.

* `phase_tau_bounds`, `wRatio_bounds`, `qedRatio_bounds`.
* `tau_lifetime_corrected`: `291.03 < τ_τ < 291.06` fs (measured `290.3 ± 0.5`; the tree row
  `291.15–291.17`). Still conditional on the measured `τ_μ` and supplied `B_e`.
-/

noncomputable section
namespace PMElementaryParticles.TauLifetimeCorrected

open PMElementaryParticles LeptonMasses MuonLifetimeCorrected

def xTau : ℝ := 1 / tau ^ 2

def phaseTau : ℝ := MassiveWidth.phase xTau

def wSq : ℝ := PMConstants.GaugeSpectrum.wMassSquared PMSubstrate.causalCoupling
  PMConstants.ElectroweakBounds.electronGeV

def eG : ℝ := PMConstants.ElectroweakBounds.electronGeV

def wRatio : ℝ := (1 + 3 * (muon * eG) ^ 2 / (5 * wSq)) / (1 + 3 * (tau * eG) ^ 2 / (5 * wSq))

def qedMu : ℝ := 1 - MuonQEDLoops.alphaR / Real.pi * (Real.pi ^ 2 / 2 - 25 / 8)

def qedTau : ℝ := 1 - (1 / 133.3) / Real.pi * (Real.pi ^ 2 / 2 - 25 / 8)

def tauLifeCorrected : ℝ := TauLifetime.tauLife * (phaseFactor / phaseTau) * wRatio * (qedMu / qedTau)

lemma xTau_eq : xTau = 1 / 3477 ^ 2 := by unfold xTau; rw [tau_value]

lemma log_xTau_bounds : (-17 : ℝ) < Real.log xTau ∧ Real.log xTau < -16 := by
  rw [xTau_eq]
  have hpos : (0 : ℝ) < 1 / 3477 ^ 2 := by norm_num
  constructor
  · rw [Real.lt_log_iff_exp_lt hpos]
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h17 : Real.exp (-17) = 1 / Real.exp 1 ^ 17 := by
      rw [← Real.exp_nat_mul, Real.exp_neg]; norm_num
    rw [h17]
    have hp : (2.7182818283 : ℝ) ^ 17 < Real.exp 1 ^ 17 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  · rw [Real.log_lt_iff_lt_exp hpos]
    have h1 : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
    have h16 : Real.exp (-16) = 1 / Real.exp 1 ^ 16 := by
      rw [← Real.exp_nat_mul, Real.exp_neg]; norm_num
    rw [h16]
    have hp : Real.exp 1 ^ 16 < (2.7182818286 : ℝ) ^ 16 :=
      pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    nlinarith

theorem phase_tau_bounds : (0.9999993 : ℝ) < phaseTau ∧ phaseTau < 0.9999994 := by
  obtain ⟨l1, l2⟩ := log_xTau_bounds
  have hx : xTau = 1 / 3477 ^ 2 := xTau_eq
  unfold phaseTau MassiveWidth.phase
  rw [hx] at l1 l2 ⊢
  constructor <;> nlinarith

theorem wRatio_bounds : (0.9996973 : ℝ) < wRatio ∧ wRatio < 0.9996975 := by
  have hw := PMConstants.ElectroweakBounds.w_squared_bounds
  have hm := muon_value
  have hW1 : (78.96 : ℝ) ^ 2 < wSq := hw.1
  have hW2 : wSq < (78.97 : ℝ) ^ 2 := hw.2
  have hwpos : 0 < wSq := lt_trans (by norm_num) hW1
  have heG : eG = 0.00051099895069 := rfl
  unfold wRatio
  rw [tau_value, heG]
  set m := muon
  have hden : 0 < 1 + 3 * (3477 * 0.00051099895069 : ℝ) ^ 2 / (5 * wSq) := by positivity
  rw [lt_div_iff₀ hden, div_lt_iff₀ hden]
  have e1 : 3 * (m * 0.00051099895069) ^ 2 / (5 * wSq) = (3 * (m * 0.00051099895069) ^ 2 / 5) * (1 / wSq) := by
    field_simp
  have e2 : 3 * (3477 * 0.00051099895069 : ℝ) ^ 2 / (5 * wSq) = (3 * (3477 * 0.00051099895069) ^ 2 / 5) * (1 / wSq) := by
    field_simp
  rw [e1, e2]
  have i1 : 1 / (78.97 : ℝ) ^ 2 < 1 / wSq := one_div_lt_one_div_of_lt hwpos hW2
  have i2 : 1 / wSq < 1 / (78.96 : ℝ) ^ 2 := one_div_lt_one_div_of_lt (by norm_num) hW1
  have hm2a : (206.7682716 : ℝ) ^ 2 < m ^ 2 := pow_lt_pow_left₀ hm.1 (by norm_num) (by norm_num)
  have hm2b : m ^ 2 < (206.7682718 : ℝ) ^ 2 := pow_lt_pow_left₀ hm.2 (by linarith [hm.1]) (by norm_num)
  have hmm : (m * 0.00051099895069) ^ 2 = m ^ 2 * 0.00051099895069 ^ 2 := by ring
  rw [hmm]
  set u := 1 / wSq
  have hu : 0 < u := by positivity
  constructor <;> nlinarith [mul_lt_mul_of_pos_right hm2a hu, mul_lt_mul_of_pos_right hm2b hu]

theorem qedRatio_bounds : (1.0000831 : ℝ) < qedMu / qedTau ∧ qedMu / qedTau < 1.0000833 := by
  obtain ⟨a1, a2⟩ := MuonQEDLoops.alphaR_div_pi_bounds
  have hp1 := MuonQEDLoops.pi_lo
  have hp2 := MuonQEDLoops.pi_hi
  have hc1 : (1.80980220054 : ℝ) < Real.pi ^ 2 / 2 - 25 / 8 := by nlinarith
  have hc2 : Real.pi ^ 2 / 2 - 25 / 8 < (1.80980220055 : ℝ) := by nlinarith
  have hb1 : (1 / 133.3 / 3.1415926535898 : ℝ) < 1 / 133.3 / Real.pi :=
    div_lt_div_of_pos_left (by norm_num) Real.pi_pos hp2
  have hb2 : 1 / 133.3 / Real.pi < (1 / 133.3 / 3.14159265358979 : ℝ) :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) hp1
  set c := Real.pi ^ 2 / 2 - 25 / 8
  set A := MuonQEDLoops.alphaR / Real.pi
  set B := 1 / 133.3 / Real.pi
  have hmu1 : (1 - 0.0023421573 * 1.80980220055 : ℝ) < qedMu := by
    unfold qedMu; change _ < 1 - A * c; nlinarith
  have hmu2 : qedMu < (1 - 0.0023421564 * 1.80980220054 : ℝ) := by
    unfold qedMu; change 1 - A * c < _; nlinarith
  have ht1 : (1 - 1 / 133.3 / 3.14159265358979 * 1.80980220055 : ℝ) < qedTau := by
    unfold qedTau; change _ < 1 - B * c; nlinarith
  have ht2 : qedTau < (1 - 1 / 133.3 / 3.1415926535898 * 1.80980220054 : ℝ) := by
    unfold qedTau; change 1 - B * c < _; nlinarith
  have htpos : 0 < qedTau := lt_trans (by norm_num) ht1
  constructor
  · rw [lt_div_iff₀ htpos]; nlinarith
  · rw [div_lt_iff₀ htpos]; nlinarith

theorem tau_lifetime_corrected : (291.03 : ℝ) < tauLifeCorrected ∧ tauLifeCorrected < 291.06 := by
  obtain ⟨t1, t2⟩ := TauLifetime.tau_lifetime_tree
  obtain ⟨f1, f2⟩ := phase_bounds
  obtain ⟨g1, g2⟩ := phase_tau_bounds
  obtain ⟨w1, w2⟩ := wRatio_bounds
  obtain ⟨q1, q2⟩ := qedRatio_bounds
  have hgpos : 0 < phaseTau := lt_trans (by norm_num) g1
  have hP1 : (0.99981353 : ℝ) < phaseFactor / phaseTau := by
    rw [lt_div_iff₀ hgpos]; nlinarith
  have hP2 : phaseFactor / phaseTau < (0.99981367 : ℝ) := by
    rw [div_lt_iff₀ hgpos]; nlinarith
  unfold tauLifeCorrected
  set T := TauLifetime.tauLife
  set P := phaseFactor / phaseTau
  set W := wRatio
  set Q := qedMu / qedTau
  have hTP1 : (291.15 : ℝ) * 0.99981353 < T * P := mul_lt_mul'' t1 hP1 (by norm_num) (by norm_num)
  have hTP2 : T * P < (291.17 : ℝ) * 0.99981367 := mul_lt_mul'' t2 hP2 (by linarith) (by linarith)
  have hTPW1 : (291.15 : ℝ) * 0.99981353 * 0.9996973 < T * P * W :=
    mul_lt_mul'' hTP1 w1 (by norm_num) (by norm_num)
  have hTPW2 : T * P * W < (291.17 : ℝ) * 0.99981367 * 0.9996975 :=
    mul_lt_mul'' hTP2 w2 (by nlinarith) (by linarith)
  have h1 : (291.15 : ℝ) * 0.99981353 * 0.9996973 * 1.0000831 < T * P * W * Q :=
    mul_lt_mul'' hTPW1 q1 (by norm_num) (by norm_num)
  have h2 : T * P * W * Q < (291.17 : ℝ) * 0.99981367 * 0.9996975 * 1.0000833 :=
    mul_lt_mul'' hTPW2 q2 (by nlinarith) (by linarith)
  constructor
  · have : (291.03 : ℝ) < 291.15 * 0.99981353 * 0.9996973 * 1.0000831 := by norm_num
    linarith
  · have : (291.17 : ℝ) * 0.99981367 * 0.9996975 * 1.0000833 < 291.06 := by norm_num
    linarith

end PMElementaryParticles.TauLifetimeCorrected
