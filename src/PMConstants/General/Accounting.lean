import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Ratios of aggregate work correspond to work-weighted individual ratios.
The identity needs no probabilistic independence. It does not identify which
observation is physical. -/
namespace PMConstants.General.Accounting
open Finset

theorem aggregate_is_work_weighted {I : Type*} [Fintype I]
    (clock work : I → ℝ) (hw : ∀ i, work i ≠ 0) :
    (∑ i, clock i)/(∑ i, work i) =
      ∑ i, (work i/(∑ j, work j))*(clock i/work i) := by
  rw [sum_div]
  apply sum_congr rfl
  intro i _
  by_cases hs : (∑ j, work j) = 0
  · simp [hs]
  · field_simp [hw i, hs]

end PMConstants.General.Accounting
