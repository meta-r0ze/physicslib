import PMAction.ConfinedCarrier
import PMAction.SplitUpdate

/-!
# The substrate walk on the confined cube

`ConfinedCarrier.axisStep_unitary` shows that the identity-completed axis step is unitary for
any Hermitian hop `N` with `N³ = N`. This file proves `N³ = N` for the walk's actual truncated hop
on a finite region, and instantiates it on the `3×3×3` cube.

* `truncHop S c = S ⊗ c + S† ⊗ c†`: the hop along one axis, with spatial shift `S` and the walk's
  coefficient `c` (`LocalUnitary.coefficient`, block-diagonal on the two sectors in
  `SplitUpdate.coefficient`). `truncHop_hermitian`.
* `truncHop_cube`: if `S S† S = S` (a partial isometry, as the open shift is) and `c² = 0`,
  `cc† + c†c = 1`, then `N³ = N`. On a periodic lattice `S` is a permutation and `N² = 1`; on a
  finite region `N²` is the projector onto the modes the hop covers.
* `shift3`, `shift3_partial`: the open shift on three sites satisfies `S S† S = S`.
* `partial_kron_left`, `partial_kron_right`: the property survives tensoring with an identity,
  so `cubeShiftX`, `cubeShiftY`, `cubeShiftZ` on `Fin 3 × Fin 3 × Fin 3` all satisfy it.
* `cube_axisStep_unitary`: on the `3×3×3` cube, every axis step `cos τ · N² + i sin τ · N +
  (1 − N²)` of the walk is unitary, for every `τ`.
-/

noncomputable section
namespace PMAction.ConfinedWalk
open Matrix
open scoped Kronecker

section General
variable {X K : Type*} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]

/-- The truncated hop along one axis. -/
def truncHop (S : Matrix X X ℂ) (c : Matrix K K ℂ) : Matrix (X × K) (X × K) ℂ :=
  S ⊗ₖ c + Sᴴ ⊗ₖ cᴴ

omit [Fintype X] [Fintype K] [DecidableEq X] [DecidableEq K] in
theorem truncHop_hermitian (S : Matrix X X ℂ) (c : Matrix K K ℂ) :
    (truncHop S c).IsHermitian := by
  simp [IsHermitian, truncHop, conjTranspose_add, conjTranspose_kronecker, add_comm]

omit [DecidableEq X] [DecidableEq K] in
lemma triple (A B C : Matrix X X ℂ) (a b c : Matrix K K ℂ) :
    A ⊗ₖ a * B ⊗ₖ b * C ⊗ₖ c = (A * B * C) ⊗ₖ (a * b * c) := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul]

/-- **The truncated hop cubes to itself.** -/
theorem truncHop_cube (S : Matrix X X ℂ) (c : Matrix K K ℂ) (hS : S * Sᴴ * S = S)
    (hc : c * c = 0) (h1 : c * cᴴ + cᴴ * c = 1) :
    truncHop S c * truncHop S c * truncHop S c = truncHop S c := by
  have hcd : cᴴ * cᴴ = 0 := by rw [← conjTranspose_mul, hc, conjTranspose_zero]
  have hp : c * cᴴ * c = c := ConfinedCarrier.coefficient_partial c cᴴ hc h1
  have hp' : cᴴ * c * cᴴ = cᴴ :=
    ConfinedCarrier.coefficient_partial cᴴ c hcd (by rw [add_comm]; exact h1)
  have hS' : Sᴴ * S * Sᴴ = Sᴴ := by
    have h := congrArg conjTranspose hS
    simpa [conjTranspose_mul, Matrix.mul_assoc] using h
  have z1 : c * c * c = 0 := by rw [hc, zero_mul]
  have z2 : c * c * cᴴ = 0 := by rw [hc, zero_mul]
  have z3 : c * cᴴ * cᴴ = 0 := by rw [Matrix.mul_assoc, hcd, Matrix.mul_zero]
  have z4 : cᴴ * c * c = 0 := by rw [Matrix.mul_assoc, hc, Matrix.mul_zero]
  have z5 : cᴴ * cᴴ * c = 0 := by rw [hcd, zero_mul]
  have z6 : cᴴ * cᴴ * cᴴ = 0 := by rw [hcd, zero_mul]
  unfold truncHop
  simp only [add_mul, mul_add, triple, z1, z2, z3, z4, z5, z6, hp, hp', hS, hS', kronecker_zero,
    zero_add, add_zero]

omit [DecidableEq X] in
theorem partial_kron_left (S : Matrix X X ℂ) (hS : S * Sᴴ * S = S) :
    (S ⊗ₖ (1 : Matrix K K ℂ)) * (S ⊗ₖ (1 : Matrix K K ℂ))ᴴ * (S ⊗ₖ (1 : Matrix K K ℂ)) =
      S ⊗ₖ (1 : Matrix K K ℂ) := by
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, hS, one_mul]

omit [DecidableEq X] in
theorem partial_kron_right (S : Matrix X X ℂ) (hS : S * Sᴴ * S = S) :
    ((1 : Matrix K K ℂ) ⊗ₖ S) * ((1 : Matrix K K ℂ) ⊗ₖ S)ᴴ * ((1 : Matrix K K ℂ) ⊗ₖ S) =
      (1 : Matrix K K ℂ) ⊗ₖ S := by
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, hS, one_mul]

end General

/-! ## The `3×3×3` cube -/

/-- The open shift on three sites, `|x+1⟩⟨x|`. -/
def shift3 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 1, 0, 0; 0, 1, 0]

theorem shift3_partial : shift3 * shift3ᴴ * shift3 = shift3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shift3, Matrix.mul_apply, Fin.sum_univ_three, conjTranspose_apply, Matrix.vecMul,
      dotProduct]

abbrev Cube := Fin 3 × Fin 3 × Fin 3

def cubeShiftX : Matrix Cube Cube ℂ := shift3 ⊗ₖ (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
def cubeShiftY : Matrix Cube Cube ℂ :=
  (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ (shift3 ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))
def cubeShiftZ : Matrix Cube Cube ℂ :=
  (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ shift3)

theorem cubeShiftX_partial : cubeShiftX * cubeShiftXᴴ * cubeShiftX = cubeShiftX :=
  partial_kron_left shift3 shift3_partial

theorem cubeShiftY_partial : cubeShiftY * cubeShiftYᴴ * cubeShiftY = cubeShiftY :=
  partial_kron_right _ (partial_kron_left shift3 shift3_partial)

theorem cubeShiftZ_partial : cubeShiftZ * cubeShiftZᴴ * cubeShiftZ = cubeShiftZ :=
  partial_kron_right _ (partial_kron_right shift3 shift3_partial)

/-- **The walk on the cube is unitary.** For any partial-isometry shift (in particular
`cubeShiftX/Y/Z`) and any axis coefficient `SplitUpdate.coefficient j`, the identity-completed
axis step `cos τ · N² + i sin τ · N + (1 − N²)` is unitary. -/
theorem cube_axisStep_unitary {X : Type*} [Fintype X] [DecidableEq X] (S : Matrix X X ℂ)
    (hS : S * Sᴴ * S = S) (j : Fin 3) (τ : ℝ) :
    (ConfinedCarrier.axisStep (truncHop S (SplitUpdate.coefficient j)) (Real.cos τ)
        (Complex.I * Real.sin τ))ᴴ *
      ConfinedCarrier.axisStep (truncHop S (SplitUpdate.coefficient j)) (Real.cos τ)
        (Complex.I * Real.sin τ) = 1 :=
  ConfinedCarrier.axisStep_unitary' _ (truncHop_hermitian _ _)
    (truncHop_cube _ _ hS (SplitUpdate.coefficient_relations j).1
      (SplitUpdate.coefficient_relations j).2) τ

end PMAction.ConfinedWalk
