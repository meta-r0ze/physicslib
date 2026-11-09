import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# The algebraic core of Osterwalder–Schrader reconstruction

The finite-volume Osterwalder–Schrader (OS) step turns a Euclidean reflection-positive measure into
a physical Hilbert space. The integral measure-theory side of the gauge branch is in
`PMAction.ReciprocalReflection`: the physical reciprocal-link law `gibbs`, the OS form

`osForm F G = ∫ F ω · conj(G (θω)) dgibbs`

with `θ` the site reflection, and the positivity axiom `reflection_positive'` (the diagonal
`osForm F F` is real and non-negative for upper observables). This file supplies the *algebraic*
core that converts those facts into a semi-inner-product:

* `conj_symm_of_real_diag`: a sesquilinear form whose diagonal is real is automatically
  **Hermitian**, `B x y = conj (B y x)` (polarization). Applying it to `osForm` — sesquilinear by
  integral linearity, real diagonal by `reflection_positive'` — makes the OS form Hermitian.

With Hermitian-ness the OS form is a semi-inner-product. The two remaining steps toward the
physical Hilbert space — the Cauchy–Schwarz bound `‖B x y‖² ≤ Re (B x x) · Re (B y y)` (which
makes the null set `{x | B x x = 0}` a subspace) and the quotient by it — are scoped in
`PMAction/REVIEW-AND-NEXT.md`; neither is built here.

The framework here is the standard finite-dimensional OS reconstruction, specialized to the data
`ReciprocalReflection` actually proves. No continuum, infinite-volume or mass-gap claim is made.
-/

noncomputable section
namespace PMAction.OsterwalderSchrader

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **A sesquilinear form with real diagonal is Hermitian.** This is the polarization step of OS
reconstruction: linearity in the first argument, conjugate-linearity in the second, and a real
diagonal force `B x y = conj (B y x)`. -/
theorem conj_symm_of_real_diag (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z)
    (hsmul₁ : ∀ (a : ℂ) x y, B (a • x) y = a * B x y)
    (hsmul₂ : ∀ (a : ℂ) x y, B x (a • y) = star a * B x y)
    (hre : ∀ x, (B x x).im = 0) :
    ∀ x y, B x y = star (B y x) := by
  intro x y
  have e1 : B (x + y) (x + y) = B x x + B x y + B y x + B y y := by
    rw [hadd₁ x y (x + y), hadd₂ x x y, hadd₂ y x y]
    abel
  have h1 : (B x y).im + (B y x).im = 0 := by
    have h := hre (x + y)
    rw [e1] at h
    simp only [Complex.add_im] at h
    linarith [hre x, hre y, h]
  have hvv : B (Complex.I • y) (Complex.I • y) = B y y := by
    rw [hsmul₁ Complex.I y (Complex.I • y), hsmul₂ Complex.I y y,
      Complex.star_def, Complex.conj_I]
    rw [show Complex.I * (-Complex.I * B y y) = -(Complex.I * Complex.I) * B y y by ring,
      Complex.I_mul_I]
    ring
  have e2 : B (x + Complex.I • y) (x + Complex.I • y) =
      B x x + (-Complex.I) * B x y + Complex.I * B y x + B y y := by
    rw [hadd₁ x (Complex.I • y) (x + Complex.I • y), hadd₂ x x (Complex.I • y),
      hadd₂ (Complex.I • y) x (Complex.I • y), hvv, hsmul₁ Complex.I y x,
      hsmul₂ Complex.I x y, Complex.star_def, Complex.conj_I]
    abel
  have h2 : (B y x).re = (B x y).re := by
    have h := hre (x + Complex.I • y)
    rw [e2] at h
    simp only [Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, hre x, hre y, zero_mul, one_mul,
      neg_one_mul, add_zero, zero_add] at h
    linarith
  apply Complex.ext
  · rw [Complex.star_def, Complex.conj_re]; exact h2.symm
  · simp only [Complex.star_def, Complex.conj_im]
    linarith

end PMAction.OsterwalderSchrader
