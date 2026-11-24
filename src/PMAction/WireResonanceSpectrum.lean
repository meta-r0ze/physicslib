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

/-- The normalized direct row and two separately calibrated restoring rows,
with a static insertion at address 2. -/
def massWithRates (k₁ k₂ offset : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1, 0, 1; k₁, -k₁, 0; 0, k₂, k₂ * (offset - 1)]

/-- Equal restoring coefficients recover the symmetric benchmark. -/
def mass (k offset : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := massWithRates k k offset

theorem mass_eq (k offset : ℝ) :
    (mass k offset).map (fun x : ℝ => (x : ℂ)) =
      WireMass.mass (-1) ![1, k, k] ![1, 1, 1] +
        diagonal ![0, 0, ((k * offset : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mass, massWithRates, WireMass.mass, WireMass.shift, ReferenceWallRotation.X, CyclicSeesaw.cyc,
      diagonal_mul]
  ring

/-- Squared mass operator with independent restoring coefficients. -/
def gramWithRates (k₁ k₂ offset : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  massWithRates k₁ k₂ offset * (massWithRates k₁ k₂ offset)ᵀ

/-- Squared mass operator at the common restoring coefficient. -/
def gram (k offset : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := gramWithRates k k offset

private theorem gram_entries (k₁ k₂ offset : ℝ) :
    gramWithRates k₁ k₂ offset =
      !![2, -k₁, k₂ * (offset - 1);
        -k₁, 2 * k₁ ^ 2, -k₁ * k₂;
        k₂ * (offset - 1), -k₁ * k₂, k₂ ^ 2 * (1 + (offset - 1) ^ 2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramWithRates, massWithRates, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.transpose_apply] <;> ring

/-- The secular cubic retains the two restoring coefficients separately. -/
theorem char_eval_with_rates (k₁ k₂ offset t : ℝ) :
    (gramWithRates k₁ k₂ offset).charpoly.eval t =
      t ^ 3 - (2 + 2 * k₁ ^ 2 + k₂ ^ 2 * (1 + (offset - 1) ^ 2)) * t ^ 2 +
        (3 * k₁ ^ 2 + k₂ ^ 2 * (2 + (offset - 1) ^ 2) +
          k₁ ^ 2 * k₂ ^ 2 * (1 + 2 * (offset - 1) ^ 2)) * t -
        k₁ ^ 2 * k₂ ^ 2 * offset ^ 2 := by
  rw [Matrix.eval_charpoly, gram_entries, Matrix.det_fin_three]
  simp [Matrix.scalar_apply, Matrix.sub_apply]
  ring

/-- Characteristic polynomial for the common-rate benchmark. -/
theorem char_eval (k offset t : ℝ) :
    (gram k offset).charpoly.eval t =
      t ^ 3 - (2 + k ^ 2 * (3 + (offset - 1) ^ 2)) * t ^ 2 +
        (k ^ 2 * (5 + (offset - 1) ^ 2) + k ^ 4 * (1 + 2 * (offset - 1) ^ 2)) * t -
        k ^ 4 * offset ^ 2 := by
  rw [gram, char_eval_with_rates]
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

/-- For the bare resonant wire, the exact square of the middle-to-heavy ratio
can be expressed without square roots. -/
theorem bare_ratio_sq (k : ℝ) :
    (Real.sqrt (3 * k ^ 2) / Real.sqrt (2 + k ^ 2)) ^ 2 =
      3 * k ^ 2 / (2 + k ^ 2) := by
  rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]

/-- Invert the normalized bare Schur ratio for a pulse whose common-duration
coefficient is `rate` and whose direct/restoring duration ratio is `d`. -/
theorem bare_duration_ratio_sq {r rate d : ℝ} (hRate : rate ≠ 0)
    (hRatio : r = Real.sqrt (3 * (rate * d) ^ 2) / Real.sqrt (2 + (rate * d) ^ 2)) :
    d ^ 2 = 2 * r ^ 2 / ((3 - r ^ 2) * rate ^ 2) := by
  have hsq := congrArg (fun x : ℝ => x ^ 2) hRatio
  rw [bare_ratio_sq, eq_div_iff (by positivity : 2 + (rate * d) ^ 2 ≠ 0)] at hsq
  have hthree : 3 - r ^ 2 ≠ 0 := by
    intro he
    have hr : r ^ 2 = 3 := by linarith only [he]
    rw [hr] at hsq
    nlinarith only [hsq]
  apply (eq_div_iff (mul_ne_zero hthree (pow_ne_zero _ hRate))).2
  linear_combination -hsq

end PMAction.WireResonanceSpectrum
