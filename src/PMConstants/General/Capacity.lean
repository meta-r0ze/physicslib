import Mathlib.Tactic

/-! General capacity constraints, independent of the vacuum example.
Work is divisible in this model. Amounts are measured over one specified
deadline interval; worker capacity means the work executable in that interval.
Deferral, dropping work and relaxing the deadline are excluded by `complete`.
-/
namespace PMConstants.General.Capacity
open Finset

variable {Tasks Workers : Type*} [Fintype Tasks] [Fintype Workers]

def Feasible (demand : Tasks → ℝ) (capacity overhead : Workers → ℝ)
    (service : Tasks → Workers → ℝ) : Prop :=
  (∀ i j, 0 ≤ service i j) ∧
    (∀ i, ∑ j, service i j = demand i) ∧
    (∀ j, (∑ i, service i j) + overhead j ≤ capacity j)

/-- A feasible division respects the total budget, including interface cost. -/
theorem total_budget (demand : Tasks → ℝ) (capacity overhead : Workers → ℝ)
    (service : Tasks → Workers → ℝ) (h : Feasible demand capacity overhead service) :
    (∑ i, demand i) + (∑ j, overhead j) ≤ ∑ j, capacity j := by
  obtain ⟨-, hcomplete, hworker⟩ := h
  calc
    _ = (∑ i, ∑ j, service i j) + (∑ j, overhead j) := by simp_rw [hcomplete]
    _ = ∑ j, ((∑ i, service i j) + overhead j) := by rw [sum_comm, sum_add_distrib]
    _ ≤ _ := sum_le_sum (fun j _ => hworker j)

/-- Splitting an unchanged insufficient total budget cannot remove overload. -/
theorem no_allocation_under_overload (demand : Tasks → ℝ)
    (capacity overhead : Workers → ℝ) (hcost : ∀ j, 0 ≤ overhead j)
    (hover : (∑ j, capacity j) < ∑ i, demand i) :
    ¬ ∃ service, Feasible demand capacity overhead service := by
  rintro ⟨service, h⟩
  have hb := total_budget demand capacity overhead service h
  have ho : 0 ≤ ∑ j, overhead j := sum_nonneg (fun j _ => hcost j)
  linarith

/-- Additional workers must supply enough *additional* capacity. This is a
necessary bound, not a proof that every task schedule meeting it is feasible. -/
theorem worker_count_bound (demand : Tasks → ℝ) (overhead : Workers → ℝ)
    (service : Tasks → Workers → ℝ) (C : ℝ) (hC : 0 < C)
    (h : Feasible demand (fun _ => C) overhead service) :
    ((∑ i, demand i) + (∑ j, overhead j))/C ≤ Fintype.card Workers := by
  apply (div_le_iff₀ hC).mpr
  simpa using total_budget demand (fun _ => C) overhead service h

/-- A continuum of distinct divisions can obey the same capacity constraints. -/
theorem feasible_family (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    Feasible (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 2 => (1 : ℝ))
      (fun _ => 0) (fun _ j => if j = 0 then p else 1-p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; dsimp; split_ifs <;> linarith
  · intro i; norm_num [Fin.sum_univ_succ]
  · intro j; fin_cases j <;> norm_num [Fin.sum_univ_succ] <;> linarith

/-- Persistence feasibility does not imply full utilization of every worker. -/
theorem feasible_with_idle_capacity :
    Feasible (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 2 => (1 : ℝ))
      (fun _ => 0) (fun _ j => if j = 0 then 1 else 0) ∧
      (∑ _i : Fin 1, (1 : ℝ)) < ∑ _j : Fin 2, (1 : ℝ) := by
  constructor
  · simpa using feasible_family 1 (by norm_num) (by norm_num)
  · norm_num

end PMConstants.General.Capacity
