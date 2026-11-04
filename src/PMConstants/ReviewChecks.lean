import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace PMConstants.ReviewChecks
open scoped Kronecker

/-- Tensor products multiply the two traces: ranks 8 and 3 give 24, not 11. -/
theorem tensor_trace_check :
    Matrix.trace ((1 : Matrix (Fin 8) (Fin 8) ℝ) ⊗ₖ
      (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 24 := by
  rw [Matrix.trace_kronecker]
  norm_num

/-- An idempotent projection has only eigenvalues zero and one. A proposed φ²
"projection eigenvalue" needs a different, explicitly specified operator. -/
theorem projection_eigenvalue {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : V →ₗ[ℝ] V) (hP : P.comp P = P) (v : V) (hv : v ≠ 0)
    (t : ℝ) (ht : P v = t • v) : t = 0 ∨ t = 1 := by
  have h := congrArg (fun f : V →ₗ[ℝ] V => f v) hP
  simp only [LinearMap.comp_apply, ht, map_smul, smul_smul] at h
  have hz : (t*t-t) • v = 0 := by rw [sub_smul, h, sub_self]
  have heq : t*t-t = 0 := (smul_eq_zero.mp hz).resolve_right hv
  rcases mul_eq_zero.mp (show t*(t-1) = 0 by nlinarith [heq]) with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

end PMConstants.ReviewChecks
