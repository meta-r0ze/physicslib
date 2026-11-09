import PMElementaryParticles.TauLifetime

/-!
# Tau-lifetime measured pull (moved from the PMElementaryParticles leaf)

The tree-level tau lifetime `tauLife` and its E8-only enclosure stay in
`PMElementaryParticles.TauLifetime`; the PDG measured comparison lives here.

With the standard small corrections (electron phase space in the muon, W
propagator in the tau, the difference of the QED corrections at the two masses)
entering as a factor `c ∈ [0.9995, 0.9997]`, the pull against PDG `290.3 ± 0.5` fs,
combined with the `B_e` error (`±0.65` fs) as `0.82` fs, lies in `(0.8, 1.0)σ`.
-/

noncomputable section
namespace E8PConstants.TauLifetimePulls
open PMElementaryParticles.TauLifetime

theorem tau_lifetime_pull (c : ℝ) (hc : 0.9995 ≤ c ∧ c ≤ 0.9997) :
    0.8 < (c * tauLife - 290.3) / 0.82 ∧ (c * tauLife - 290.3) / 0.82 < 1.0 := by
  have h := tau_lifetime_tree
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith [h.1, hc.1]
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith [h.2, hc.2]

end E8PConstants.TauLifetimePulls
