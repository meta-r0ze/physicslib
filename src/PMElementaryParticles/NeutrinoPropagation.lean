import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! **Two-flavour neutrino propagation interface.**

The mass-squared splitting and mixing angle are inputs; the oscillation phase and
survival probability are the standard two-flavour consequences.  This is the
structural propagation law, not a derivation of the neutrino mass spectrum.
-/

noncomputable section
namespace PMElementaryParticles.NeutrinoPropagation

/-- Two-flavour mass and mixing data. -/
structure TwoFlavour where
  m1 : ℝ
  m2 : ℝ
  theta : ℝ

def deltaM21sq (ν : TwoFlavour) : ℝ := ν.m2 ^ 2 - ν.m1 ^ 2

/-- Oscillation phase `Δm² L/(4E)`. -/
def phase (ν : TwoFlavour) (L E : ℝ) : ℝ :=
  deltaM21sq ν * L / (4 * E)

/-- Two-flavour survival probability. -/
def survival (ν : TwoFlavour) (L E : ℝ) : ℝ :=
  1 - Real.sin (2 * ν.theta) ^ 2 * Real.sin (phase ν L E) ^ 2

/-- Two-flavour transition probability. -/
def transition (ν : TwoFlavour) (L E : ℝ) : ℝ :=
  Real.sin (2 * ν.theta) ^ 2 * Real.sin (phase ν L E) ^ 2

theorem transition_nonneg (ν : TwoFlavour) (L E : ℝ) : 0 ≤ transition ν L E := by
  unfold transition
  positivity

theorem transition_le_one (ν : TwoFlavour) (L E : ℝ) : transition ν L E ≤ 1 := by
  unfold transition
  have h1 : Real.sin (2 * ν.theta) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  have h2 : Real.sin (phase ν L E) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  nlinarith [sq_nonneg (Real.sin (2 * ν.theta)), sq_nonneg (Real.sin (phase ν L E))]

theorem survival_nonneg (ν : TwoFlavour) (L E : ℝ) : 0 ≤ survival ν L E := by
  unfold survival
  have ht := transition_le_one ν L E
  unfold transition at ht
  linarith

theorem survival_le_one (ν : TwoFlavour) (L E : ℝ) : survival ν L E ≤ 1 := by
  unfold survival
  have ht := transition_nonneg ν L E
  unfold transition at ht
  linarith

theorem survival_add_transition (ν : TwoFlavour) (L E : ℝ) :
    survival ν L E + transition ν L E = 1 := by
  unfold survival transition
  ring

end PMElementaryParticles.NeutrinoPropagation
