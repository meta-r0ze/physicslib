import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Coherent phase action and incoherent cost action

The same operational action has two projections:

```
phase weight  = exp(i phase)          (coherent sector)
cost weight   = exp(−β cost)          (incoherent sector)
combined      = exp(i phase − β cost)
```

The phase factor has unit modulus; the cost factor carries the survival
attenuation.
-/

noncomputable section
namespace PersistenceMechanics.CoherentAction

open Complex

/-- Coherent phase weight. -/
def phaseWeight (phase : ℝ) : ℂ :=
  Complex.exp ((phase : ℂ) * Complex.I)

/-- Incoherent cost weight. -/
def costWeight (β cost : ℝ) : ℝ :=
  Real.exp (-β * cost)

/-- Combined coherent/incoherent weight. -/
def combinedWeight (phase β cost : ℝ) : ℂ :=
  phaseWeight phase * (costWeight β cost : ℂ)

theorem phaseWeight_normSq (phase : ℝ) :
    Complex.normSq (phaseWeight phase) = 1 := by
  unfold phaseWeight
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem combinedWeight_normSq (phase β cost : ℝ) :
    Complex.normSq (combinedWeight phase β cost) = (costWeight β cost) ^ 2 := by
  unfold combinedWeight
  rw [Complex.normSq_mul, phaseWeight_normSq]
  simp [pow_two]

/-- Quality factor: phase frequency over attenuation rate. -/
def qualityFactor (phaseRate β costRate : ℝ) : ℝ :=
  phaseRate / (β * costRate)

end PersistenceMechanics.CoherentAction
