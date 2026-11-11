import PMConstants.ScalarSector

/-!
# The scalar ledger picks the same channel accounting

The regulatory ledger behind `λ = (3 − 1/43)/23` counts `23 = ν + σ + χ` intrinsic labels.
`VevAccounting` and `GravityAccounting` found that the scale formulas persist only with `ν` as the
channel frame. Counting the channels as payload instead, `16η + 7`, gives
`λ_p = (3 − 1/43)/(16η + 7)`.

* `payload_higgs`: with the measured Fermi constant, `λ_p` gives `125.52 < m_H < 125.53` GeV.
* `payload_pull`: that is more than `2.8σ` above `125.20 ± 0.11` GeV, while the frame count is
  within `0.75σ` (`higgs_pull`, below).

Three precision observables (`G_F`, `G`, `m_H` with `G_F`) therefore select the same accounting.
-/

noncomputable section
namespace E8PConstants.ScalarAccounting
open PMConstants
open PMConstants ScalarSector

def lambdaPayload : ℝ :=
  (((PMSubstrate.E8Values.sigma : ℝ) - (PMSubstrate.E8Values.chi : ℝ)) -
      1 / (PMSubstrate.E8Values.Delta : ℝ)) /
    ((PMSubstrate.E8Values.nu : ℝ) * overhead + (PMSubstrate.E8Values.D : ℝ) +
      (PMSubstrate.E8Values.sigma : ℝ) - (PMSubstrate.E8Values.chi : ℝ))

def higgsSqPayload (GF : ℝ) : ℝ := 2 * lambdaPayload / (Real.sqrt 2 * GF)

theorem payload_higgs {GF : ℝ} (h : 1.1663782e-5 < GF ∧ GF < 1.1663794e-5) :
    125.52 < Real.sqrt (higgsSqPayload GF) ∧ Real.sqrt (higgsSqPayload GF) < 125.53 := by
  have hs := JointConstants.sqrt_two_bounds
  have hd : 0 < Real.sqrt 2 * GF := by nlinarith [hs.1, h.1]
  have hlo : (125.52 : ℝ)^2 < higgsSqPayload GF := by
    unfold higgsSqPayload lambdaPayload overhead
    rw [PMSubstrate.E8Values.overhead_eq, PMSubstrate.E8Values.nu_eq,
      PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq,
      PMSubstrate.E8Values.Delta_eq, PMSubstrate.E8Values.D_eq, lt_div_iff₀ hd]
    nlinarith [hs.2, h.2]
  have hhi : higgsSqPayload GF < (125.53 : ℝ)^2 := by
    unfold higgsSqPayload lambdaPayload overhead
    rw [PMSubstrate.E8Values.overhead_eq, PMSubstrate.E8Values.nu_eq,
      PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq,
      PMSubstrate.E8Values.Delta_eq, PMSubstrate.E8Values.D_eq, div_lt_iff₀ hd]
    nlinarith [hs.1, h.1]
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; exact hlo
  · rw [Real.sqrt_lt' (by norm_num)]; exact hhi

theorem payload_pull {GF : ℝ} (h : 1.1663782e-5 < GF ∧ GF < 1.1663794e-5) :
    2.8 < (Real.sqrt (higgsSqPayload GF) - 125.20) / 0.11 := by
  have hm := payload_higgs h
  rw [lt_div_iff₀ (by norm_num)]; linarith

/-- The frame count's Higgs pull against `m_H = 125.20 ± 0.11` GeV (PDG 2024), moved
here from `PMConstants.ScalarSector`. -/
theorem higgs_pull {GF : ℝ} (h : 1.1663782e-5 < GF ∧ GF < 1.1663794e-5) :
    0.5 < (Real.sqrt (higgsSq GF) - 125.20) / 0.11 ∧ (Real.sqrt (higgsSq GF) - 125.20) / 0.11 < 0.75 := by
  have hm := higgs_from_fermi h
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

end ScalarAccounting
