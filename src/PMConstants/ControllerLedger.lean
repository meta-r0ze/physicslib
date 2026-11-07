import PMConstants.TypedRepairWork
import Mathlib.Order.SetNotation

/-! **Experimental/candidate module.**

# Controller candidate/cost ledger

The finite controller candidates are the typed repair lengths in
`TypedRepairWork`.  The cost is the active primitive-work count.  Persistence
selects the least-cost candidate subject to the stated arithmetic constraints.

This packages the existing arithmetic bounds as explicit least-cost selection
statements.  It does not claim that the candidate family or the work count is the
final physical controller implementation.
-/

noncomputable section
namespace PMConstants.ControllerLedger

open PMConstants.TypedRepairWork

/-- A controller candidate is a typed repair vector. -/
abbrev ControllerCandidate := Repairs

/-- Controller cost: active primitive-work count. -/
def controllerCost (r : ControllerCandidate) : ℕ := activeBudget r

/-- Baseline admissibility: all gauge-active repairs positive. -/
def BaselineAdmissible (r : ControllerCandidate) : Prop := Positive r

/-- Target-mixing admissibility. -/
def TargetAdmissible (r : ControllerCandidate) : Prop :=
  Positive r ∧ 4 * r.q = 4 * r.u + r.d + 3 * r.e

/-- All-equal admissibility. -/
def AllEqualAdmissible (r : ControllerCandidate) : Prop :=
  Positive r ∧ r.q + r.l = r.u + r.d ∧
    4 * r.q = 4 * r.u + r.d + 3 * r.e

/-- Persistence selects the baseline least-cost controller. -/
theorem baseline_controller_least :
    IsLeast {c : ℕ | ∃ r : ControllerCandidate,
      BaselineAdmissible r ∧ controllerCost r = c} 15 := by
  constructor
  · refine ⟨⟨1, 1, 1, 1, 1, 0⟩, ?_, ?_⟩
    · norm_num [BaselineAdmissible, Positive]
    · norm_num [controllerCost, activeBudget]
  · rintro c ⟨r, hr, hc⟩
    rw [← hc]
    exact baseline_bound r hr

/-- Persistence selects the target-mixing least-cost controller. -/
theorem target_controller_least :
    IsLeast {c : ℕ | ∃ r : ControllerCandidate,
      TargetAdmissible r ∧ controllerCost r = c} 21 := by
  constructor
  · refine ⟨weakWitness, ?_, ?_⟩
    · norm_num [TargetAdmissible, Positive, weakWitness]
    · norm_num [controllerCost, activeBudget, weakWitness]
  · rintro c ⟨r, hr, hc⟩
    rw [← hc]
    exact target_budget_bound r hr.1 hr.2

/-- Persistence selects the all-equal least-cost controller. -/
theorem allEqual_controller_least :
    IsLeast {c : ℕ | ∃ r : ControllerCandidate,
      AllEqualAdmissible r ∧ controllerCost r = c} 43 := by
  constructor
  · refine ⟨equalWitness, ?_, ?_⟩
    · norm_num [AllEqualAdmissible, Positive, equalWitness]
    · norm_num [controllerCost, activeBudget, equalWitness]
  · rintro c ⟨r, hr, hc⟩
    rw [← hc]
    exact all_equal_budget_bound r hr.1 hr.2.1 hr.2.2

end PMConstants.ControllerLedger
