import PMSubstrate.E8Values
import Mathlib.Tactic

/-! **Substrate module.**

# E8 phase margin

The boundary gap `χ` leaves `Δ−χ` surviving clock phases:

```
phaseMargin = (Δ−χ)/Δ = 41/43.
```
-/

noncomputable section
namespace PMSubstrate.E8Margin

def phaseMargin : ℝ :=
  (((PMSubstrate.E8Values.Delta - PMSubstrate.E8Values.chi : Nat)) : ℝ) /
    (PMSubstrate.E8Values.Delta : ℝ)

theorem phaseMargin_eq : phaseMargin = 41 / 43 := by
  unfold phaseMargin
  norm_num [PMSubstrate.E8Values.Delta, PMSubstrate.E8Values.chi,
    PMSubstrate.baseline]

theorem phaseMargin_pos : 0 < phaseMargin := by
  rw [phaseMargin_eq]; norm_num

/-- Apply the E8 phase margin to a channel weight. -/
noncomputable def phaseCorrected (weight : ℝ) : ℝ := phaseMargin * weight

theorem phaseCorrected_eq (weight : ℝ) :
    phaseCorrected weight = phaseMargin * weight := rfl

end PMSubstrate.E8Margin
