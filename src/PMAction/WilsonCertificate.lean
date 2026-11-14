import PMAction.InertiaCertificate
import PMAction.InertiaCongruence

/-! A certificate for a Hermitian kernel using a square candidate basis.
Strict dominance of the transformed matrix proves that both factors are
nonsingular, so the checker does not require a separate Gram estimate. -/
noncomputable section
namespace PMAction.InertiaCertificate
open Matrix Finset PMAction.InertiaStability

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The sign count and invertibility needed by the winding witness, even when
the candidate basis was obtained numerically. -/
theorem wilson_certificate {H Q B : Matrix n n ℂ} (hH : H.IsHermitian)
    (basis : B = Qᴴ * H * Q)
    (gap : ∀ i, ∑ j ∈ univ.erase i, ‖B i j‖ < ‖B i i‖) :
    H.det ≠ 0 ∧ negCount hH = (univ.filter fun i => (B i i).re < 0).card := by
  subst B
  have nonsing := det_ne_zero_of_sum_row_lt_diag gap
  rw [det_mul, det_mul] at nonsing
  have hQ := (mul_ne_zero_iff.mp nonsing).2
  have hdet := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp nonsing).1).2
  exact ⟨hdet, (negCount_congruence hH hdet Q hQ).symm.trans
    (negCount_eq_sign_count (isHermitian_conjTranspose_mul_mul Q hH) gap)⟩

/-- A global bound on squared off-diagonal entries can certify every row.
The dimension factor uses the number of off-diagonal entries in that row. -/
theorem row_gap_of_squared_error (B : Matrix n n ℂ) (errSq : ℝ)
    (herr : ∑ i, ∑ j ∈ univ.erase i, ‖B i j‖ ^ 2 ≤ errSq)
    (margin : ∀ i, ((univ.erase i).card : ℝ) * errSq < ‖B i i‖ ^ 2) (i : n) :
    ∑ j ∈ univ.erase i, ‖B i j‖ < ‖B i i‖ := by
  let s := univ.erase i
  have hrow : ∑ j ∈ s, ‖B i j‖ ^ 2 ≤ errSq := by
    exact (single_le_sum (f := fun k => ∑ j ∈ univ.erase k, ‖B k j‖ ^ 2)
      (fun k _ => by positivity) (mem_univ i)).trans herr
  have cs := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun j => ‖B i j‖)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at cs
  have hs := cs.trans_lt ((mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg s.card)).trans_lt (margin i))
  exact lt_of_not_ge (fun h => (not_lt_of_ge (pow_le_pow_left₀ (norm_nonneg _) h 2)) hs)

/-- Interface for interval certificates that bound the off-diagonal Frobenius error. -/
theorem wilson_certificate_of_squared_error {H Q B : Matrix n n ℂ} (hH : H.IsHermitian)
    (basis : B = Qᴴ * H * Q) (errSq : ℝ)
    (herr : ∑ i, ∑ j ∈ univ.erase i, ‖B i j‖ ^ 2 ≤ errSq)
    (margin : ∀ i, ((univ.erase i).card : ℝ) * errSq < ‖B i i‖ ^ 2) :
    H.det ≠ 0 ∧ negCount hH = (univ.filter fun i => (B i i).re < 0).card :=
  wilson_certificate hH basis (row_gap_of_squared_error B errSq herr margin)

end PMAction.InertiaCertificate
