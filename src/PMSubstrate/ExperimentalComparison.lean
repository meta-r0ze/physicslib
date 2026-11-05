import PMSubstrate.Impedance

/-!
# Experimental comparison leaf

The measured α values and uncertainties below are comparison inputs copied from
the cited sources. They are not used by the PMSubstrate derivation and should not
be imported by derivation modules.

This module is intentionally a leaf: it depends on the certified enclosure of
`geometricIndex`, but nothing in the main substrate proof depends on it.
-/

namespace PMSubstrate

/-- Certified deviations, in units of the quoted standard uncertainty, for the
four comparison inputs in the manuscript's table. Each lies within rounding of
the stated value. -/
theorem alpha_deviations :
    (0.575 : ℝ) < (geometricIndex - 137.035999206) / 0.000000011 ∧
      (geometricIndex - 137.035999206) / 0.000000011 < 0.585 ∧
    (3.085 : ℝ) < (geometricIndex - 137.035999166) / 0.000000015 ∧
      (geometricIndex - 137.035999166) / 0.000000015 < 3.095 ∧
    (6.155 : ℝ) < (geometricIndex - 137.035999046) / 0.000000027 ∧
      (geometricIndex - 137.035999046) / 0.000000027 < 6.165 ∧
    (1.675 : ℝ) < (geometricIndex - 137.035999177) / 0.000000021 ∧
      (geometricIndex - 137.035999177) / 0.000000021 < 1.685 := by
  obtain ⟨hlo, hhi⟩ := geometricIndex_bounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  first
  | (rw [lt_div_iff₀ (by norm_num)]; linarith)
  | (rw [div_lt_iff₀ (by norm_num)]; linarith)

end PMSubstrate
