import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Dirichlet cube eigenvalue

The separable Dirichlet eigenvalue of the `n×n×n` cube, `λ_{abc} = 6 − 2cos(πa/(n+1)) −
2cos(πb/(n+1)) − 2cos(πc/(n+1))`. This is the only object the tree consumes from the former
spectral-response module: the finite beta spectral rate (`PMAtoms.BetaLattice`) uses it as the mode
energy. The spectral Green function and the uniform-charge response that the module once
scaffolded was an unused alternative route and has been removed.
-/

noncomputable section
namespace PMAtoms

/-- Dirichlet eigenvalue of the `n×n×n` cube. -/
def dirichletEigenvalue (n a b c : Nat) : ℝ :=
  6
    - 2 * Real.cos (Real.pi * a / (n + 1))
    - 2 * Real.cos (Real.pi * b / (n + 1))
    - 2 * Real.cos (Real.pi * c / (n + 1))

end PMAtoms
