import Mathlib.Tactic

/-! Finite nesting depth requires a discrete descent or a positive uniform
per-level resource floor. Positivity of each individual real cost is insufficient.
No finite-total-node conclusion is asserted without a branching/count assumption.
-/
namespace PMConstants.General.Hierarchy
open Finset

theorem depth_bound (cost : ℕ → ℝ) (floor budget : ℝ) (n : ℕ)
    (hf : 0 < floor) (hcost : ∀ i < n, floor ≤ cost i)
    (hbudget : ∑ i ∈ range n, cost i ≤ budget) : (n : ℝ) ≤ budget/floor := by
  apply (le_div_iff₀ hf).mpr
  calc
    (n : ℝ)*floor = ∑ _i ∈ range n, floor := by simp
    _ ≤ ∑ i ∈ range n, cost i := sum_le_sum (fun i hi => hcost i (mem_range.mp hi))
    _ ≤ budget := hbudget

theorem no_infinite_floor (cost : ℕ → ℝ) (floor budget : ℝ) (hf : 0 < floor)
    (hcost : ∀ i, floor ≤ cost i) :
    ¬ ∀ n, ∑ i ∈ range n, cost i ≤ budget := by
  intro hb
  obtain ⟨n, hn⟩ := exists_nat_gt (budget/floor)
  have h := depth_bound cost floor budget n hf (fun i _ => hcost i) (hb n)
  linarith

theorem geometric_partial_sum (n : ℕ) :
    (∑ i ∈ range n, (1/2 : ℝ)^(i+1)) = 1-(1/2 : ℝ)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring

/-- An infinite sequence of strictly positive costs can have all finite
prefixes within one budget. A uniform floor cannot be omitted. -/
theorem positive_costs_do_not_bound_depth :
    (∀ i : ℕ, 0 < (1/2 : ℝ)^(i+1)) ∧
      ∀ n : ℕ, (∑ i ∈ range n, (1/2 : ℝ)^(i+1)) ≤ 1 := by
  constructor
  · intro i; positivity
  · intro n; rw [geometric_partial_sum]; have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) n; linarith

/-- For natural-valued resources each strict descent consumes at least one
unit, giving a depth bound without a real-valued minimum-cost assumption. -/
theorem discrete_depth_bound (remaining : ℕ → ℕ) (n : ℕ)
    (hstep : ∀ i < n, remaining (i+1) < remaining i) : remaining n+n ≤ remaining 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := hstep n (by omega)
    have hprev := ih (fun i hi => hstep i (by omega))
    omega

end PMConstants.General.Hierarchy
