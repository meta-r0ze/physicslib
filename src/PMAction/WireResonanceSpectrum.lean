import PMAction.WireMass
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Spectrum of the normalized wire at resonance and with a static insertion

The stationary-reference mass has a reference factor with rows `(1, k, k)`
and an other-wall cycle of unit strength. At real resonance the detuning is
`-1`. Allow a real shift on static address 2. The characteristic polynomial
of the squared mass then gives every mode, including the terms that the
determinant alone omits.
-/

noncomputable section
namespace PMAction.WireResonanceSpectrum

open Matrix

/-- Real matrix of the normalized stationary-reference wire, with a shift
in the other-wall detuning at address 2. -/
def mass (k offset : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1, 0, 1; k, -k, 0; 0, k, k * (offset - 1)]

theorem mass_eq (k offset : ℝ) :
    (mass k offset).map (fun x : ℝ => (x : ℂ)) =
      WireMass.mass (-1) ![1, k, k] ![1, 1, 1] +
        diagonal ![0, 0, ((k * offset : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mass, WireMass.mass, WireMass.shift, ReferenceWallRotation.X, CyclicSeesaw.cyc,
      diagonal_mul]
  ring

/-- Squared mass operator of the real wire. -/
def gram (k offset : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  mass k offset * (mass k offset)ᵀ

private theorem gram_entries (k offset : ℝ) :
    gram k offset =
      !![2, -k, k * (offset - 1);
        -k, 2 * k ^ 2, -k ^ 2;
        k * (offset - 1), -k ^ 2, k ^ 2 * (1 + (offset - 1) ^ 2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, mass, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;> ring

/-- Characteristic polynomial evaluated at a trial squared mass. -/
theorem char_eval (k offset t : ℝ) :
    (gram k offset).charpoly.eval t =
      t ^ 3 - (2 + k ^ 2 * (3 + (offset - 1) ^ 2)) * t ^ 2 +
        (k ^ 2 * (5 + (offset - 1) ^ 2) + k ^ 4 * (1 + 2 * (offset - 1) ^ 2)) * t -
        k ^ 4 * offset ^ 2 := by
  rw [Matrix.eval_charpoly, gram_entries, Matrix.det_fin_three]
  simp [Matrix.scalar_apply, Matrix.sub_apply]
  ring

/-- At resonance, the squared singular values are exactly `0`, `3k²`,
and `2 + k²`. The two positive roots are distinct for `0 < k < 1`. -/
theorem bare_spectrum (k t : ℝ) :
    t ∈ spectrum ℝ (gram k 0) ↔ t = 0 ∨ t = 3 * k ^ 2 ∨ t = 2 + k ^ 2 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, char_eval]
  have h :
      t ^ 3 - (2 + k ^ 2 * (3 + ((0 : ℝ) - 1) ^ 2)) * t ^ 2 +
          (k ^ 2 * (5 + ((0 : ℝ) - 1) ^ 2) +
            k ^ 4 * (1 + 2 * ((0 : ℝ) - 1) ^ 2)) * t - k ^ 4 * 0 ^ 2 =
        t * (t - 3 * k ^ 2) * (t - (2 + k ^ 2)) := by ring
  rw [h, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero, or_assoc]

/-- The nonnegative masses of the bare Schur operator, expressed through
the spectrum of its Gram matrix. -/
theorem bare_mass_spectrum (k m : ℝ) (hm : 0 ≤ m) :
    m ^ 2 ∈ spectrum ℝ (gram k 0) ↔
      m = 0 ∨ m = Real.sqrt (3 * k ^ 2) ∨ m = Real.sqrt (2 + k ^ 2) := by
  have eq_root (t : ℝ) (ht : 0 ≤ t) : m ^ 2 = t ↔ m = Real.sqrt t := by
    conv_lhs => rhs; rw [← Real.sq_sqrt ht]
    exact sq_eq_sq₀ hm (Real.sqrt_nonneg _)
  rw [bare_spectrum, pow_eq_zero_iff two_ne_zero, eq_root _ (by positivity),
    eq_root _ (by positivity)]

end PMAction.WireResonanceSpectrum
