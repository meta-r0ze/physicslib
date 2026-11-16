import PMAction.LatticeSiteAction
import PMAction.FinitePolarization

/-!
# Reciprocal-cell measure from the existing D₄ site basis

The reciprocal basis is fixed by its pairing with the physical site basis.
For N periods in each primitive direction the real-space volume is
2 a⁴ N⁴ and each momentum sample has Fourier weight 1/(2 a⁴ N⁴).
The coordinate-period grid in FinitePolarization has different periods;
identifying its physical domain is a separate boundary-condition question.
-/
noncomputable section
namespace PMAction.D4MomentumMeasure
open Matrix LatticeSiteAction Real

def siteBasis (a : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := a • basisR
def reciprocalBasis (a : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (2 * Real.pi / a) • basisInv.transpose

lemma inverse_det : basisInv.det = 1/2 := by
  have h := congrArg Matrix.det basis_mul_inv
  rw [Matrix.det_mul, basis_det, Matrix.det_one] at h
  linarith

/-- The dual basis pairs with the existing site generators by 2π. -/
theorem dual_pairing {a : ℝ} (ha : a ≠ 0) :
    (siteBasis a).transpose * reciprocalBasis a = (2 * Real.pi) • 1 := by
  have hi : basisR.transpose * basisInv.transpose = 1 := by
    rw [← Matrix.transpose_mul, inv_mul_basis, Matrix.transpose_one]
  simp only [siteBasis, reciprocalBasis, Matrix.transpose_smul, smul_mul_smul_comm, hi]
  congr 1
  field_simp

/-- The physical site pairing uniquely determines the reciprocal basis. -/
theorem reciprocal_unique {a : ℝ} (ha : a ≠ 0) (C : Matrix (Fin 4) (Fin 4) ℝ)
    (h : (siteBasis a).transpose * C = (2 * Real.pi) • 1) : C = reciprocalBasis a := by
  let L := (1/a) • basisInv.transpose
  have hi : L * (siteBasis a).transpose = 1 := by
    have hh : basisInv.transpose * basisR.transpose = 1 := by
      rw [← Matrix.transpose_mul, basis_mul_inv, Matrix.transpose_one]
    simp [L, siteBasis, Matrix.transpose_smul, hh, ha]
  calc
    C = L * ((siteBasis a).transpose * C) := by rw [← Matrix.mul_assoc, hi, one_mul]
    _ = L * ((siteBasis a).transpose * reciprocalBasis a) := by rw [h, dual_pairing ha]
    _ = reciprocalBasis a := by rw [← Matrix.mul_assoc, hi, one_mul]

private lemma abs_four (x : ℝ) : |x|^4 = x^4 := by
  calc
    |x|^4 = (|x|^2)^2 := by ring
    _ = (x^2)^2 := by rw [sq_abs]
    _ = x^4 := by ring

theorem site_cell_volume (a : ℝ) : |(siteBasis a).det| = 2 * a^4 := by
  simp [siteBasis, basis_det, abs_mul, abs_pow, abs_four, mul_comm]

theorem reciprocal_cell_volume (a : ℝ) :
    |(reciprocalBasis a).det| = (2 * Real.pi / a)^4 / 2 := by
  simp [reciprocalBasis, Matrix.det_transpose, inverse_det, abs_mul, abs_pow, abs_four]
  ring

def momentumStep (N : ℕ) (a : ℝ) := (1 / (N : ℝ)) • reciprocalBasis a

/-- Primitive-period grid, paired with N copies of each physical site
generator. The coordinate-period grid has a different momentum map. -/
def primitiveMomentum (N : ℕ) (a : ℝ) (k : FinitePolarization.Grid N) : Fin 4 → ℝ :=
  reciprocalBasis a *ᵥ (fun i => (k i).val / (N : ℝ))

/-- Fourier normalization d⁴k/(2π)⁴ applied to one primitive-grid cell. -/
def sampleWeight (N : ℕ) (a : ℝ) : ℝ :=
  |(momentumStep N a).det| / (2 * Real.pi)^4

theorem primitive_weight (N : ℕ) [NeZero N] {a : ℝ} (ha : a ≠ 0) :
    sampleWeight N a = 1 / (2 * a^4 * (N : ℝ)^4) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hp := Real.pi_ne_zero
  unfold sampleWeight momentumStep
  rw [Matrix.det_smul, abs_mul, reciprocal_cell_volume]
  simp only [Fintype.card_fin, abs_pow, abs_one_div, abs_of_nonneg (show 0 ≤ (N : ℝ) from Nat.cast_nonneg N)]
  field_simp

/-- One primitive-grid sample is the inverse of the physical torus volume. -/
theorem inverse_torus_volume (N : ℕ) [NeZero N] {a : ℝ} (ha : a ≠ 0) :
    sampleWeight N a * (2 * a^4 * (N : ℝ)^4) = 1 := by
  rw [primitive_weight N ha]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp

theorem grid_card (N : ℕ) [NeZero N] :
    Fintype.card (FinitePolarization.Grid N) = N^4 := by
  simp [FinitePolarization.Grid]

/-- The normalized measure of all primitive momentum samples is the
inverse site-cell volume, independently of the number of periods. -/
theorem total_weight (N : ℕ) [NeZero N] {a : ℝ} (ha : a ≠ 0) :
    (Fintype.card (FinitePolarization.Grid N) : ℝ) * sampleWeight N a = 1 / (2 * a^4) := by
  rw [grid_card, primitive_weight N ha]
  push_cast
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp

end PMAction.D4MomentumMeasure
