import PersistenceMechanics.DecayChannel
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Supplied radiative correction

An explicit multiplicative correction `R` to a partial rate.  This is an
interface for comparison/radiative factors; it does not derive `R`.
-/

noncomputable section
namespace PMElementaryParticles.RadiativeCorrection

open PersistenceMechanics.Decay

def correctedRate (R rate : ℝ) : ℝ := R * rate

def correctedLifetime (R rate : ℝ) : ℝ := 1 / correctedRate R rate

theorem correctedRate_pos {R rate : ℝ} (hR : 0 < R) (hr : 0 < rate) :
    0 < correctedRate R rate := mul_pos hR hr

theorem correctedLifetime_pos {R rate : ℝ} (hR : 0 < R) (hr : 0 < rate) :
    0 < correctedLifetime R rate := by
  unfold correctedLifetime
  exact one_div_pos.mpr (correctedRate_pos hR hr)

end PMElementaryParticles.RadiativeCorrection
