import PMAction.InertiaStability
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Topology.Instances.Real.Lemmas

/-! A row-dominance certificate for deforming a Hermitian matrix to its diagonal.
The hypotheses concern the matrix in the proposed certificate basis. Transferring
the count back to the original Wilson kernel requires a separate congruence argument. -/

noncomputable section
namespace PMAction.InertiaCertificate

open Matrix Finset PMAction.InertiaStability

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Scale only the off-diagonal entries. -/
def path (B : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  fun i j => if i = j then B i i else (t : ℂ) * B i j

omit [Fintype n] in
theorem path_hermitian {B : Matrix n n ℂ} (hB : B.IsHermitian) (t : ℝ) :
    (path B t).IsHermitian := by
  ext i j
  by_cases h : i = j
  · subst j
    simpa [Matrix.conjTranspose_apply, path] using hB.apply i i
  · simpa [Matrix.conjTranspose_apply, path, h, Ne.symm h, mul_comm] using
      congrArg (fun z : ℂ => z * (t : ℂ)) (hB.apply i j)

theorem path_invertible {B : Matrix n n ℂ}
    (gap : ∀ i, ∑ j ∈ univ.erase i, ‖B i j‖ < ‖B i i‖)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : (path B t).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  calc
    ∑ j ∈ univ.erase i, ‖path B t i j‖ ≤ ∑ j ∈ univ.erase i, ‖B i j‖ := by
      apply sum_le_sum
      intro j hj
      have hij := (Finset.ne_of_mem_erase hj).symm
      simp [path, hij, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    _ < ‖path B t i i‖ := by simpa [path] using gap i

theorem negCount_eq_diagonal {B : Matrix n n ℂ} (hB : B.IsHermitian)
    (gap : ∀ i, ∑ j ∈ univ.erase i, ‖B i j‖ < ‖B i i‖) :
    negCount hB = negCount (path_hermitian hB 0) := by
  let H := fun t : Set.Icc (0 : ℝ) 1 => path B t.val
  have hc : Continuous H := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases h : i = j <;> simp [H, path, h] <;> fun_prop
  have loc := negCount_locallyConstant H hc (fun t => path_hermitian hB t.val)
    (fun t => path_invertible gap t.property)
  have eq := loc.apply_eq_of_preconnectedSpace (1 : Set.Icc (0 : ℝ) 1) 0
  have hone : path B 1 = B := by
    ext i j
    by_cases h : i = j <;> simp [path, h]
  simpa [H, hone] using eq

/-- Count negative diagonal entries with multiplicity, including repeated eigenvalues. -/
theorem diagonal_negCount (d : n → ℂ) (hd : (diagonal d).IsHermitian) :
    negCount hd = (univ.filter fun i => (d i).re < 0).card := by
  classical
  have roots := hd.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod] at roots
  · simp only [Polynomial.roots_X_sub_C] at roots
    have counts := congrArg (Multiset.countP (fun z : ℂ => z.re < 0)) roots
    simpa [Multiset.countP_map, negCount, Finset.card, Function.comp_def] using counts.symm
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- A strictly row-dominant Hermitian matrix has as many filled modes as negative diagonal entries. -/
theorem negCount_eq_sign_count {B : Matrix n n ℂ} (hB : B.IsHermitian)
    (gap : ∀ i, ∑ j ∈ univ.erase i, ‖B i j‖ < ‖B i i‖) :
    negCount hB = (univ.filter fun i => (B i i).re < 0).card := by
  have hzero : path B 0 = diagonal (fun i => B i i) := by
    ext i j
    by_cases h : i = j <;> simp [path, diagonal, h]
  refine (negCount_eq_diagonal hB gap).trans ?_
  have transport (A D : Matrix n n ℂ) (e : A = D) (hA : A.IsHermitian) :
      negCount hA = negCount (e ▸ hA : D.IsHermitian) := by
    subst D
    rfl
  exact (transport _ _ hzero (path_hermitian hB 0)).trans (diagonal_negCount _ _)

end PMAction.InertiaCertificate
