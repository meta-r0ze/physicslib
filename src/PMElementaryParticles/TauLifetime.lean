import PMElementaryParticles.LeptonMasses
import PMElementaryParticles.MuonRate

/-!
# Conditional tau lifetime

The contact-width ratio cancels the shared Fermi coupling.
The result takes a muon lifetime and an electronic branching fraction as inputs.
`tau_lifetime_tree` transports their intervals. The reporter supplies measurements.
The QED correction is supplied theory; `TauBranching` records the open hadronic factor.
-/

noncomputable section
namespace PMElementaryParticles.TauLifetime
open PMElementaryParticles.LeptonMasses

/-- **The `m⁵` law: width ratio of two leptons.** -/
theorem rate_ratio (G mμ mτ : ℝ) (hG : G ≠ 0) (hμ : mμ ≠ 0) :
    (∫ E in (0 : ℝ)..(mτ / 2), MuonRate.rate G mτ E) / (∫ E in (0 : ℝ)..(mμ / 2), MuonRate.rate G mμ E) =
      (mτ / mμ) ^ 5 := by
  rw [MuonRate.muon_rate, MuonRate.muon_rate]
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- Tau lifetime in the same time unit as the supplied muon lifetime. -/
def tauLife (muonTime electronicBranch : ℝ) : ℝ :=
  muonTime * electronicBranch * (muon / tau) ^ 5

/-- Transport supplied input intervals through the positive mass ratio. -/
theorem tau_lifetime_tree {muonTime electronicBranch lo hi blo bhi : ℝ}
    (hm : lo ≤ muonTime ∧ muonTime ≤ hi)
    (hb : blo ≤ electronicBranch ∧ electronicBranch ≤ bhi)
    (hlo : 0 ≤ lo) (hblo : 0 ≤ blo) :
    lo * blo * (muon / tau) ^ 5 ≤ tauLife muonTime electronicBranch ∧
      tauLife muonTime electronicBranch ≤ hi * bhi * (muon / tau) ^ 5 := by
  have hp : 0 ≤ (muon / tau) ^ 5 := by
    have hmu : 0 < muon := lt_trans (by norm_num) muon_value.1
    have ht : 0 < tau := by rw [tau_value]; norm_num
    positivity
  exact ⟨mul_le_mul_of_nonneg_right (mul_le_mul hm.1 hb.1 hblo (hlo.trans hm.1)) hp,
    mul_le_mul_of_nonneg_right (mul_le_mul hm.2 hb.2 (hblo.trans hb.1)
      (hlo.trans (hm.1.trans hm.2))) hp⟩

end PMElementaryParticles.TauLifetime
