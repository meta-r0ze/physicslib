import PMAtoms.LatticeSpectral

/-!
# Continuum limit of the uniform response

Scaffold for the fourth spectral target.

Target:

```lean
theorem uniformResponse_asymptotic :
    Filter.Tendsto (fun n : Nat => uniformResponse n / (n : ℝ) ^ 5)
      Filter.atTop (nhds (1 / (16 * Real.pi)))
```

The numerical sequence is

`S(3) = 743/51`, `S(4) ≈ 50.2456`, `S(5) ≈ 133.7643`, …

and `S(n)/n^5 → 1/(16π) ≈ 0.019894`.
-/

noncomputable section
namespace PMAtoms

/-- The continuum coefficient of the uniform lattice response. -/
def uniformResponseCoefficient : ℝ := 1 / (16 * Real.pi)

theorem uniformResponseCoefficient_pos : 0 < uniformResponseCoefficient := by
  unfold uniformResponseCoefficient
  positivity

end PMAtoms
