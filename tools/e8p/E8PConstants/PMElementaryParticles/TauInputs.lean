import E8PConstants.Experimental
import PMElementaryParticles.TauE8
import PMElementaryParticles.TauLifetimeCorrected
import PMElementaryParticles.PhysicalUnits

noncomputable section
namespace E8PConstants.TauValues
open PMElementaryParticles PMElementaryParticles.LeptonMasses PMElementaryParticles.MuonLifetime

def tauLife : ℝ := TauLifetime.tauLife TauInputs.muonTimeFs TauInputs.electronicBranch

/-- The same source theorem also transports the supplied measurement intervals.
The reporter's central row uses the singleton specialization below, and keeps the
branch uncertainty in its comparison uncertainty instead of counting it twice. -/
theorem supplied_input_interval :
    TauInputs.muonTimeLoFs * TauInputs.branchLo * (muon / tau) ^ 5 ≤ tauLife ∧
      tauLife ≤ TauInputs.muonTimeHiFs * TauInputs.branchHi * (muon / tau) ^ 5 :=
  TauLifetime.tau_lifetime_tree TauInputs.muonTime_interval TauInputs.branch_interval
    (by norm_num [TauInputs.muonTimeLoFs]) (by norm_num [TauInputs.branchLo])

theorem tau_lifetime_tree : 291.15 < tauLife ∧ tauLife < 291.17 := by
  have hm := muon_value
  have ht := tau_value
  have hinput := TauLifetime.tau_lifetime_tree TauInputs.muonTime_point_interval
    TauInputs.branch_point_interval (by norm_num [TauInputs.muonTimeFs])
    (by norm_num [TauInputs.electronicBranch])
  change TauInputs.muonTimeFs * TauInputs.electronicBranch * (muon / tau) ^ 5 ≤ tauLife ∧
    tauLife ≤ TauInputs.muonTimeFs * TauInputs.electronicBranch * (muon / tau) ^ 5 at hinput
  rw [ht] at hinput
  have hr1 : (206.7682716 / 3477 : ℝ) < muon / 3477 := by
    apply div_lt_div_of_pos_right hm.1 (by norm_num)
  have hr2 : muon / 3477 < (206.7682718 / 3477 : ℝ) := by
    apply div_lt_div_of_pos_right hm.2 (by norm_num)
  have p1 : (206.7682716 / 3477 : ℝ) ^ 5 < (muon / 3477) ^ 5 :=
    pow_lt_pow_left₀ hr1 (by norm_num) (by norm_num)
  have p2 : (muon / 3477) ^ 5 < (206.7682718 / 3477 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ hr2 (by positivity) (by norm_num)
  constructor
  · apply lt_of_lt_of_le _ hinput.1
    norm_num [TauInputs.muonTimeFs, TauInputs.electronicBranch]
    nlinarith [p1]
  · apply lt_of_le_of_lt hinput.2
    norm_num [TauInputs.muonTimeFs, TauInputs.electronicBranch]
    nlinarith [p2]


def tauLifetimeE8 : ℝ := PMElementaryParticles.TauE8.tauLifetimeE8 TauInputs.electronicBranch

theorem tauLifetimeE8_bounds :
    (1.6e8 : ℝ) < tauLifetimeE8 ∧ tauLifetimeE8 < 3.4e8 := by
  have hm := muonLifetime_bounds
  have hmu := muon_value
  have ht : tau = 3477 := tau_value
  have hr1 : (0.0594 : ℝ) < muon / tau := by
    rw [ht]; rw [lt_div_iff₀ (by norm_num)]; nlinarith [hmu.1]
  have hr2 : muon / tau < (0.0595 : ℝ) := by
    rw [ht]; rw [div_lt_iff₀ (by norm_num)]; nlinarith [hmu.2]
  have hrpos : (0 : ℝ) ≤ muon / tau := by positivity
  have h5lo : (0.0594 : ℝ) ^ 5 < (muon / tau) ^ 5 := by
    exact pow_lt_pow_left₀ hr1 (by norm_num : (0:ℝ) ≤ (0.0594:ℝ))
      (by norm_num : (5:ℕ) ≠ 0)
  have h5hi : (muon / tau) ^ 5 < (0.0595 : ℝ) ^ 5 := by
    exact pow_lt_pow_left₀ hr2 hrpos (by norm_num : (5:ℕ) ≠ 0)
  have hmlo : (0:ℝ) < muonLifetime := lt_trans (by norm_num) hm.1
  have hb : (0:ℝ) < 0.1782 := by norm_num
  have hprodlo : muonLifetime * (0.0594 : ℝ)^5 < muonLifetime * (muon / tau)^5 :=
    mul_lt_mul_of_pos_left h5lo hmlo
  have hprodhi : muonLifetime * (muon / tau)^5 < muonLifetime * (0.0595 : ℝ)^5 :=
    mul_lt_mul_of_pos_left h5hi hmlo
  have hinput := PMElementaryParticles.TauE8.tauLifetimeE8_bounds TauInputs.branch_point_interval
  change muonLifetime * (muon / tau) ^ 5 * TauInputs.electronicBranch ≤ tauLifetimeE8 ∧
    tauLifetimeE8 ≤ muonLifetime * (muon / tau) ^ 5 * TauInputs.electronicBranch at hinput
  constructor
  · apply lt_of_lt_of_le _ hinput.1
    norm_num [TauInputs.electronicBranch]
    nlinarith [hm.1, hprodlo]
  · apply lt_of_le_of_lt hinput.2
    norm_num [TauInputs.electronicBranch]
    nlinarith [hm.2, hprodhi]


def tauLifeCorrected : ℝ :=
  TauLifetimeCorrected.tauLifeCorrected TauInputs.muonTimeFs TauInputs.electronicBranch

theorem tau_lifetime_corrected : 291.01 < tauLifeCorrected ∧ tauLifeCorrected < 291.04 :=
  TauLifetimeCorrected.tau_lifetime_corrected _ _ tau_lifetime_tree

end E8PConstants.TauValues
