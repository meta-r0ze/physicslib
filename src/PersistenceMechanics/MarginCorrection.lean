import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Supplied margin correction

A finite multiplicative margin/self-energy correction to a channel weight.
This is the substrate-language replacement for an imported radiative correction.
-/

noncomputable section
namespace PersistenceMechanics.MarginCorrection

def correctedWeight (margin weight : ℝ) : ℝ := margin * weight

def correctedRate (margin rate : ℝ) : ℝ := margin * rate

theorem correctedWeight_pos {margin weight : ℝ} (hm : 0 < margin) (hw : 0 < weight) :
    0 < correctedWeight margin weight := mul_pos hm hw

theorem correctedRate_pos {margin rate : ℝ} (hm : 0 < margin) (hr : 0 < rate) :
    0 < correctedRate margin rate := mul_pos hm hr

end PersistenceMechanics.MarginCorrection
