import PersistenceMechanics.CoherentAction
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Effective phase/cost action

Physics usually writes a complex effective action:

```
S_eff = S_phase − i Γ/2 · t.
```

PM writes the same amplitude split as:

```
amplitude = exp(i φ − (β/2) S_cost)
probability = |amplitude|² = exp(−β S_cost).
```

Thus the operational width is `Γ = β · cKf`.
-/

noncomputable section
namespace PersistenceMechanics.EffectiveAction

open PersistenceMechanics.CoherentAction
open Complex

/-- Half-attenuation amplitude weight. -/
def attenuationWeight (β cost : ℝ) : ℝ :=
  Real.exp (-(β * cost) / 2)

/-- Coherent/incoherent amplitude with the correct probability normalization. -/
def amplitude (phase β cost : ℝ) : ℂ :=
  phaseWeight phase * (attenuationWeight β cost : ℂ)

/-- The probability obtained from the amplitude. -/
theorem amplitude_normSq (phase β cost : ℝ) :
    Complex.normSq (amplitude phase β cost) = Real.exp (-(β * cost)) := by
  unfold amplitude attenuationWeight
  rw [Complex.normSq_mul, phaseWeight_normSq]
  rw [Complex.normSq_ofReal]
  rw [← Real.exp_add]
  ring_nf

/-- Operational width from the cost rate. -/
def width (β cost time : ℝ) : ℝ := β * cost / time

/-- Phase-loss rate, kept separate from population decay. -/
def decoherenceRate (β phaseCost time : ℝ) : ℝ := β * phaseCost / time

end PersistenceMechanics.EffectiveAction
