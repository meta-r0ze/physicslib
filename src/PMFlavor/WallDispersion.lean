import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Relativistic wall dispersion interface

Physical wall energies use `E(p,m) = √(p²+m²)`, not the raw link eigenvalues.
The absolute momentum and masses remain physical inputs.
-/

noncomputable section
namespace PMFlavor.WallDispersion

/-- Relativistic wall energy. -/
def wallEnergy (p m : ℝ) : ℝ := Real.sqrt (p ^ 2 + m ^ 2)

theorem wallEnergy_nonneg (p m : ℝ) : 0 ≤ wallEnergy p m :=
  Real.sqrt_nonneg _

theorem wallEnergy_zero_mass (p : ℝ) (hp : 0 ≤ p) :
    wallEnergy p 0 = p := by
  unfold wallEnergy
  rw [show p ^ 2 + 0 ^ 2 = p ^ 2 by ring, Real.sqrt_sq hp]

/-- Spread between two wall branches. -/
def wallSpread (p m0 m2 : ℝ) : ℝ :=
  wallEnergy p m2 - wallEnergy p m0

theorem wallSpread_nonneg {p m0 m2 : ℝ} (h0 : 0 ≤ m0) (h : m0 ≤ m2) :
    0 ≤ wallSpread p m0 m2 := by
  unfold wallSpread
  apply sub_nonneg.mpr
  apply Real.sqrt_le_sqrt
  nlinarith

theorem wallSpread_zero (p m : ℝ) : wallSpread p m m = 0 := by
  unfold wallSpread
  ring

end PMFlavor.WallDispersion
