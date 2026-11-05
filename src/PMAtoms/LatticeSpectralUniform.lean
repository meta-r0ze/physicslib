import PMAtoms.LatticeSpectral

/-!
# Uniform-charge spectral response

Only odd sine modes contribute to a uniform charge, and each coordinate
contributes the cotangent transform `cot(πk/(2(n+1)))`.
-/

noncomputable section
namespace PMAtoms

/-- The uniform response is already in its odd-mode/cotangent form. -/
theorem uniformResponse_odd (n : Nat) :
    uniformResponse n =
      (2 / ((n : ℝ) + 1)) ^ 3 *
        ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
          if (a.val + 1) % 2 = 1 ∧
             (b.val + 1) % 2 = 1 ∧
             (c.val + 1) % 2 = 1 then
            (1 / Real.tan (Real.pi * (a.val + 1) / (2 * ((n : ℝ) + 1))) *
             1 / Real.tan (Real.pi * (b.val + 1) / (2 * ((n : ℝ) + 1))) *
             1 / Real.tan (Real.pi * (c.val + 1) / (2 * ((n : ℝ) + 1)))) ^ 2 /
            dirichletEigenvalue n (a.val + 1) (b.val + 1) (c.val + 1)
          else 0 := rfl

/-- Odd-mode-only uniform response, the same object as `uniformResponse`. -/
def uniformResponseOdd (n : Nat) : ℝ :=
  (2 / ((n : ℝ) + 1)) ^ 3 *
    ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
      if (a.val + 1) % 2 = 1 ∧
         (b.val + 1) % 2 = 1 ∧
         (c.val + 1) % 2 = 1 then
        (1 / Real.tan (Real.pi * (a.val + 1) / (2 * ((n : ℝ) + 1))) *
         1 / Real.tan (Real.pi * (b.val + 1) / (2 * ((n : ℝ) + 1))) *
         1 / Real.tan (Real.pi * (c.val + 1) / (2 * ((n : ℝ) + 1)))) ^ 2 /
        dirichletEigenvalue n (a.val + 1) (b.val + 1) (c.val + 1)
      else 0

theorem uniformResponse_eq_odd (n : Nat) :
    uniformResponse n = uniformResponseOdd n := rfl

end PMAtoms
