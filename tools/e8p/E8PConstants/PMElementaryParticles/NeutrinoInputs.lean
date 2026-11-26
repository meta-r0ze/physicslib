import E8PConstants.Experimental
import PMElementaryParticles.NeutrinoContext

/-! Oscillation comparison inputs applied to the EP conditional certificates. -/
noncomputable section
namespace E8PConstants.NeutrinoInputs
open PMElementaryParticles.NeutrinoContext

theorem weak_minus_rest_excluded :
    17 < ((6 * mRest) ^ 2 - mRest ^ 2 - OscillationInputs.atmospheric) /
      OscillationInputs.atmosphericSigma :=
  PMElementaryParticles.NeutrinoContext.weak_minus_rest_excluded
    (by norm_num [OscillationInputs.atmosphericSigma])
    (by norm_num [OscillationInputs.atmospheric, OscillationInputs.atmosphericSigma])

theorem weak_squared_excluded :
    (0.003052 : ℝ) < (6 * mRest) ^ 2 ∧ (6 * mRest) ^ 2 < 0.003054 ∧
      20 < ((6 * mRest) ^ 2 - OscillationInputs.atmospheric) /
        OscillationInputs.atmosphericSigma :=
  PMElementaryParticles.NeutrinoContext.weak_squared_excluded
    (by norm_num [OscillationInputs.atmosphericSigma])
    (by norm_num [OscillationInputs.atmospheric, OscillationInputs.atmosphericSigma])

theorem atmospheric_factor (k : ℝ) (hk : 0 < k)
    (hfit : (k ^ 2 - 1) * mRest ^ 2 = OscillationInputs.atmospheric) :
    5.55 < k ∧ k < 5.57 :=
  PMElementaryParticles.NeutrinoContext.atmospheric_factor k _ hk hfit
    (by norm_num [OscillationInputs.atmospheric]) (by norm_num [OscillationInputs.atmospheric])

end E8PConstants.NeutrinoInputs
