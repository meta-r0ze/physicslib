import PMAtoms.FissionAsymmetry
import PMAtoms.AlphaFinite
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Finite fission rate scaffold

Uses the same `cKf` attempt as the collective channel and an E8 cost scale

```
C_f = Δ²/(ν+D+σ+χ) = 1849/27.
```

This is only a scale test: it has no fissility/Q dependence yet.
-/

noncomputable section
namespace PMAtoms

def fissionCostScale : ℝ :=
  ((Δ : ℝ) ^ 2) / (((ν + D + σ + χ : Nat)) : ℝ)

theorem fissionCostScale_eq : fissionCostScale = 1849 / 27 := by
  unfold fissionCostScale
  norm_num [Δ, ν, D, σ, χ, PMSubstrate.baseline]

theorem fissionCostScale_pos : 0 < fissionCostScale := by
  rw [fissionCostScale_eq]; norm_num

noncomputable def fissionActivation : ℝ :=
  Real.exp (-fissionCostScale)

theorem fissionActivation_pos : 0 < fissionActivation := by
  unfold fissionActivation
  positivity

noncomputable def fissionRateScale (p : Nuclide) : ℝ :=
  alphaAttempt p * fissionActivation

theorem fissionRateScale_pos {p : Nuclide} (hZ : 0 < p.Z) (hN : 0 < p.N) :
    0 < fissionRateScale p :=
  mul_pos (alphaAttempt_pos hZ hN) fissionActivation_pos

noncomputable def fissionLifetimeScale (p : Nuclide) : ℝ :=
  1 / fissionRateScale p

end PMAtoms
