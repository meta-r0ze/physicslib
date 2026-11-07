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
def tauLifetimeE8 : ℝ :=
  muonLifetime * (muon / tau) ^ 5 * 0.1782

theorem tauLifetimeE8_pos : 0 < tauLifetimeE8 := by
  unfold tauLifetimeE8
  have hm : 0 < muon := by linarith [muon_value.1]
  have ht : 0 < tau := by rw [tau_value]; norm_num
  have hr : 0 < muon / tau := div_pos hm ht
  have hp : 0 < (muon / tau) ^ 5 := pow_pos hr 5
  have hb : (0 : ℝ) < 0.1782 := by norm_num
  exact mul_pos (mul_pos muonLifetime_pos hp) hb

/-- `TauE8` and `TauLifetime` differ only by the muon-lifetime unit/input:
the E8-input rate divided by the natural muon lifetime is the same as the
measured-muon-input rate divided by `2.1969811e9` fs. -/
theorem tauLifetimeE8_relation :
    tauLifetimeE8 / muonLifetime =
      PMElementaryParticles.TauLifetime.tauLife / 2.1969811e9 := by
  unfold tauLifetimeE8 PMElementaryParticles.TauLifetime.tauLife
  have hlt : muonLifetime ≠ 0 := ne_of_gt muonLifetime_pos
  field_simp [hlt]


/-- Certified broad enclosure of the E8-input tau lifetime in `m_e⁻¹` natural units. -/
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
  unfold tauLifetimeE8
  constructor <;> nlinarith [hm.1, hm.2, hprodlo, hprodhi, hb]

end PMElementaryParticles.TauE8
