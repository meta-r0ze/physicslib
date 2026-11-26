import PMElementaryParticles.MuonLifetime
import PMElementaryParticles.LeptonMasses
import PMElementaryParticles.TauLifetime
import Mathlib.Tactic

/-! **Comparison / E8-input check.**

Tau lifetime from the E8-input muon lifetime and E8 lepton masses, using the
leptonic branching ratio as a supplied comparison input.
-/

noncomputable section
namespace PMElementaryParticles.TauE8

open PMElementaryParticles.LeptonMasses
open PMElementaryParticles.MuonLifetime

/-- Tree-level tau lifetime from the E8-input muon lifetime. -/
def tauLifetimeE8 (electronicBranch : ℝ) : ℝ :=
  muonLifetime * (muon / tau) ^ 5 * electronicBranch

theorem tauLifetimeE8_pos {electronicBranch : ℝ} (hb : 0 < electronicBranch) :
    0 < tauLifetimeE8 electronicBranch := by
  unfold tauLifetimeE8
  have hm : 0 < muon := by linarith [muon_value.1]
  have ht : 0 < tau := by rw [tau_value]; norm_num
  have hr : 0 < muon / tau := div_pos hm ht
  have hp : 0 < (muon / tau) ^ 5 := pow_pos hr 5
  exact mul_pos (mul_pos muonLifetime_pos hp) hb

/-- Both lifetime forms share the same supplied electronic branch. -/
theorem tauLifetimeE8_relation (electronicBranch muonTime : ℝ) (ht : muonTime ≠ 0) :
    tauLifetimeE8 electronicBranch / muonLifetime =
      TauLifetime.tauLife muonTime electronicBranch / muonTime := by
  unfold tauLifetimeE8 TauLifetime.tauLife
  field_simp [muonLifetime_pos.ne']

/-- Bounds for a supplied electronic branching interval. -/
theorem tauLifetimeE8_bounds {electronicBranch blo bhi : ℝ}
    (hb : blo ≤ electronicBranch ∧ electronicBranch ≤ bhi) :
    muonLifetime * (muon / tau) ^ 5 * blo ≤ tauLifetimeE8 electronicBranch ∧
      tauLifetimeE8 electronicBranch ≤ muonLifetime * (muon / tau) ^ 5 * bhi := by
  have hm : 0 < muon := lt_trans (by norm_num) muon_value.1
  have ht : 0 < tau := by rw [tau_value]; norm_num
  unfold tauLifetimeE8
  have hp : 0 ≤ muonLifetime * (muon / tau) ^ 5 := by
    exact mul_nonneg muonLifetime_pos.le (pow_nonneg (div_pos hm ht).le _)
  exact ⟨mul_le_mul_of_nonneg_left hb.1 hp, mul_le_mul_of_nonneg_left hb.2 hp⟩

end PMElementaryParticles.TauE8
