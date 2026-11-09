import PMAtoms.LatticeSpectral

/-!
# Spectral Green identity

The spectral sum is the inverse Dirichlet Laplacian. The proof needs the 1D
sine orthogonality

`∑_{k=1}^{n} sin(πa k/(n+1)) sin(πb k/(n+1)) = (n+1)/2 · δ_{ab}`,

which is built here from the Dirichlet cosine sum `cosSum` (`∑ cos(πm k/(n+1))`)
and Mathlib's `Real.sin_mul_sum_cos`.
-/

noncomputable section
namespace PMAtoms
open Finset

/-- The Dirichlet cosine sum `∑_{k=1}^{n} cos(π m k / (n+1))`. -/
def cosSum (n m : ℕ) : ℝ :=
  ∑ k : Fin n, Real.cos (Real.pi * m * (k.val + 1) / (n + 1))

theorem cosSum_zero (n : ℕ) : cosSum n 0 = n := by
  simp [cosSum]

/-- **Evaluation of the Dirichlet cosine sum.** For `1 ≤ m < 2(n+1)`,
`∑_{k=1}^{n} cos(π m k/(n+1)) = -cos²(π m/2)`, which is `-1` for even `m` and `0` for odd `m`. -/
theorem cosSum_eq (n m : ℕ) (hm : 1 ≤ m) (hmN : m < 2 * (n + 1)) :
    cosSum n m = -Real.cos (Real.pi * (m : ℝ) / 2) ^ 2 := by
  set N : ℝ := (n : ℝ) + 1 with hN
  set A : ℝ := Real.pi * m / N with hA
  have hNpos : 0 < N := by rw [hN]; positivity
  have hconv : cosSum n m = ∑ i ∈ Finset.range n, Real.cos (A * i + A) := by
    rw [cosSum, Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    rw [dif_pos (Finset.mem_range.mp hi)]
    apply congrArg Real.cos
    simp only [hA, hN]
    push_cast
    ring
  have hmain := Real.sin_mul_sum_cos n A A
  rw [← hconv] at hmain
  have harg1 : ((n : ℝ) - 1) * A / 2 + A = Real.pi * m / 2 := by
    rw [hA, hN]; field_simp; ring
  have harg2 : (n : ℝ) * A / 2 = Real.pi * m / 2 - A / 2 := by
    rw [hA, hN]; field_simp; ring
  rw [harg1, harg2, Real.sin_sub] at hmain
  have hsp : Real.sin (Real.pi * m / 2) * Real.cos (Real.pi * m / 2) = 0 := by
    have h2 := Real.sin_two_mul (Real.pi * m / 2)
    rw [show 2 * (Real.pi * m / 2) = (m : ℝ) * Real.pi by ring, Real.sin_nat_mul_pi] at h2
    linarith
  have hrhs : (Real.sin (Real.pi * m / 2) * Real.cos (A / 2) -
        Real.cos (Real.pi * m / 2) * Real.sin (A / 2)) * Real.cos (Real.pi * m / 2) =
      -Real.cos (Real.pi * m / 2) ^ 2 * Real.sin (A / 2) := by
    linear_combination (Real.cos (A / 2)) * hsp
  rw [hrhs] at hmain
  have hsin : Real.sin (A / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · rw [hA, hN]
      have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      positivity
    · rw [hA, hN, div_lt_iff₀ (by norm_num : (0 : ℝ) < 2),
        div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      have : (m : ℝ) < 2 * ((n : ℝ) + 1) := by exact_mod_cast hmN
      nlinarith [Real.pi_pos]
  have h := hmain
  rw [mul_comm (-Real.cos (Real.pi * m / 2) ^ 2) (Real.sin (A / 2))] at h
  exact mul_left_cancel₀ hsin h

/-- For even `m`, the Dirichlet cosine sum is `-1`. -/
theorem cosSum_even (n m : ℕ) (hm : 1 ≤ m) (hmN : m < 2 * (n + 1)) (he : m % 2 = 0) :
    cosSum n m = -1 := by
  rw [cosSum_eq n m hm hmN]
  obtain ⟨k, rfl⟩ := Nat.dvd_iff_mod_eq_zero.mpr he
  have h1 : Real.cos (Real.pi * ((2 * k : ℕ) : ℝ) / 2) ^ 2 = 1 := by
    rw [show Real.pi * ((2 * k : ℕ) : ℝ) / 2 = (k : ℝ) * Real.pi by push_cast; ring,
      Real.cos_nat_mul_pi]
    rw [sq, ← pow_add, show k + k = 2 * k by ring, pow_mul, neg_one_sq, one_pow]
  rw [h1]

/-- For odd `m`, the Dirichlet cosine sum is `0`. -/
theorem cosSum_odd (n m : ℕ) (hm : 1 ≤ m) (hmN : m < 2 * (n + 1)) (ho : m % 2 = 1) :
    cosSum n m = 0 := by
  rw [cosSum_eq n m hm hmN]
  have hmk : m = 2 * (m / 2) + 1 := by omega
  have hcos : Real.cos (Real.pi * (m : ℝ) / 2) = 0 := by
    rw [hmk]
    push_cast
    rw [show Real.pi * (2 * ((m / 2 : ℕ) : ℝ) + 1) / 2 =
        ((m / 2 : ℕ) : ℝ) * Real.pi + Real.pi / 2 by ring, Real.cos_add, Real.cos_nat_mul_pi,
      Real.sin_nat_mul_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  rw [hcos]; ring

end PMAtoms
