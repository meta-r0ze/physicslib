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

/-- Lifetime after dividing by the phase margin. -/
noncomputable def phaseCorrectedLifetime (tau : ℝ) : ℝ := tau / phaseMargin

/-- Which decay family receives the phase margin. -/
inductive MarginChannel
  | beta | alpha | fission | particle
  deriving DecidableEq, Repr

/-- Current mask: the phase margin is beta-specific. -/
def marginApplies : MarginChannel → Bool
  | .beta => true
  | .alpha => false
  | .fission => false
  | .particle => false

/-- Apply the margin only when the channel mask allows it. -/
noncomputable def maskedCorrected (ch : MarginChannel) (weight : ℝ) : ℝ :=
  if marginApplies ch then phaseCorrected weight else weight

theorem maskedCorrected_beta (weight : ℝ) :
    maskedCorrected .beta weight = phaseCorrected weight := by
  unfold maskedCorrected marginApplies
  rw [ite_eq_left rfl]

theorem maskedCorrected_particle (weight : ℝ) :
    maskedCorrected .particle weight = weight := by
  unfold maskedCorrected marginApplies
  rw [ite_eq_right (by decide)]

end PMSubstrate.E8Margin
