import PMElementaryParticles.MuonLifetime
import PMElementaryParticles.LeptonMasses
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

end PMElementaryParticles.TauE8
