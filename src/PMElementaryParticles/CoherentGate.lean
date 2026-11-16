import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The coherent gate on a weak pair

`RefreshMap.feedback_injective_iff`: a Boolean gate that toggles a weak pair is reversible exactly
when both partners read the same bit. This module is the coherent version. On the pair
`(c, flipWeak c)` the toggle is the exchange; a gate of angle `φ` applies the partial exchange
`cos φ · 1 + sin φ · (exchange)` (real form; the complex form `exp(iφσₓ)` gives the same zero
set below with `i sin(b − a)`). If the partner in position `0` is gated at angle `a` and the
partner in position `1` at angle `b`, the two output columns are `col0 a` and `col1 b`.

* `cross`: their overlap is `sin (a − b)`.
* `columns_orthogonal_iff`: the gate is reversible on the pair exactly when `sin (a − b) = 0`,
  that is equal angles up to a half turn. Any gain difference between weak partners, however
  small, breaks it.
* `tensor_dot`, `recorded_orthogonal_iff`: with a record `r₀`, `r₁` written beside each output, the
  overlap is `sin (a − b) · ⟨r₀, r₁⟩`. So for unequal angles the records must be exactly
  orthogonal: one full bit of doublet position per event, independent of how small the
  difference is (`unequal_needs_orthogonal`).

**Reading.** An up/down difference in the correction gain requires every event that applies it to
export the doublet position in full. The charged-current event does this (its emitted charge
differs for the two directions); a neutral refresh does not. Candidate, not derived: the gain
difference between weak partners is carried by charged-current events.
-/

noncomputable section
namespace PMElementaryParticles.CoherentGate
open Matrix

/-- Output of the partner in position `0`, gated at angle `a`. -/
def col0 (a : ℝ) : Fin 2 → ℝ := ![Real.cos a, Real.sin a]

/-- Output of the partner in position `1`, gated at angle `b`. -/
def col1 (b : ℝ) : Fin 2 → ℝ := ![-Real.sin b, Real.cos b]

theorem col0_norm (a : ℝ) : col0 a ⬝ᵥ col0 a = 1 := by
  rw [show col0 a ⬝ᵥ col0 a = Real.cos a * Real.cos a + Real.sin a * Real.sin a by
    simp [col0, dotProduct, Fin.sum_univ_two]]
  linear_combination Real.cos_sq_add_sin_sq a

theorem col1_norm (b : ℝ) : col1 b ⬝ᵥ col1 b = 1 := by
  rw [show col1 b ⬝ᵥ col1 b = (-Real.sin b) * (-Real.sin b) + Real.cos b * Real.cos b by
    simp [col1, dotProduct, Fin.sum_univ_two]]
  linear_combination Real.sin_sq_add_cos_sq b

theorem cross (a b : ℝ) : col0 a ⬝ᵥ col1 b = Real.sin (a - b) := by
  rw [Real.sin_sub, show col0 a ⬝ᵥ col1 b = Real.cos a * (-Real.sin b) + Real.sin a * Real.cos b by
    simp [col0, col1, dotProduct, Fin.sum_univ_two]]
  ring

theorem columns_orthogonal_iff (a b : ℝ) : col0 a ⬝ᵥ col1 b = 0 ↔ Real.sin (a - b) = 0 := by
  rw [cross]

/-- An output written beside a record. -/
def tensor {n : ℕ} (u : Fin 2 → ℝ) (v : Fin n → ℝ) : Fin 2 × Fin n → ℝ := fun p => u p.1 * v p.2

theorem tensor_dot {n : ℕ} (u u' : Fin 2 → ℝ) (v v' : Fin n → ℝ) :
    tensor u v ⬝ᵥ tensor u' v' = (u ⬝ᵥ u') * (v ⬝ᵥ v') := by
  simp only [tensor, dotProduct, Fintype.sum_prod_type, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem recorded_orthogonal_iff {n : ℕ} (a b : ℝ) (r₀ r₁ : Fin n → ℝ) :
    tensor (col0 a) r₀ ⬝ᵥ tensor (col1 b) r₁ = 0 ↔ Real.sin (a - b) = 0 ∨ r₀ ⬝ᵥ r₁ = 0 := by
  rw [tensor_dot, cross, mul_eq_zero]

/-- Unequal gate angles on a weak pair force orthogonal records. -/
theorem unequal_needs_orthogonal {n : ℕ} (a b : ℝ) (r₀ r₁ : Fin n → ℝ)
    (hab : Real.sin (a - b) ≠ 0)
    (h : tensor (col0 a) r₀ ⬝ᵥ tensor (col1 b) r₁ = 0) : r₀ ⬝ᵥ r₁ = 0 :=
  ((recorded_orthogonal_iff a b r₀ r₁).mp h).resolve_left hab

end PMElementaryParticles.CoherentGate
end
