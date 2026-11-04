import PMConstants.General.Service
import PMConstants.Allocation

/-!
# Allocation from persistent finite queues

For constant arrivals and service, indefinite nonnegative bounded backlog forces
arrival = service. A common workload rate then fixes service *ratios* to demand
ratios. Full utilization additionally fixes absolute capacity fractions.

The workload vector and equal per-work-item accounting remain model inputs.
Paper III's four workload entries are exhibited explicitly rather than inferred
from the abstract existence of a persistent queue.
-/

namespace PMConstants.SteadyAllocation
open Finset

/-- Compatibility alias for the independent queue theorem. -/
theorem constant_drift_formula (q : ℕ → ℝ) (d : ℝ)
    (hstep : ∀ n, q (n+1) = q n + d) (n : ℕ) : q n = q 0 + n*d :=
  General.Service.constant_drift_formula q d hstep n

theorem bounded_drift_zero (q : ℕ → ℝ) (d C : ℝ)
    (hstep : ∀ n, q (n+1) = q n + d)
    (hbounded : ∀ n, 0 ≤ q n ∧ q n ≤ C) : d = 0 :=
  General.Service.bounded_drift_zero q d C hstep hbounded

variable {I : Type*} [Fintype I]

omit [Fintype I] in
theorem persistent_service (demand service : I → ℝ) (rate : ℝ)
    (q : I → ℕ → ℝ) (C : I → ℝ)
    (hstep : ∀ i n, q i (n+1) = q i n + rate*demand i-service i)
    (hbounded : ∀ i n, 0 ≤ q i n ∧ q i n ≤ C i) :
    ∀ i, service i = rate*demand i := by
  intro i
  have h := bounded_drift_zero (q i) (rate*demand i-service i) (C i)
    (fun n => by rw [hstep]; ring) (hbounded i)
  linarith

/-- With positive operation rate, the normalized service shares are forced
even when there is idle capacity. -/
theorem normalized_share (demand service : I → ℝ) (rate : ℝ)
    (hbalance : ∀ i, service i = rate*demand i) (hr : rate ≠ 0)
    (i : I) : service i / (∑ j, service j) = demand i / (∑ j, demand j) := by
  simp_rw [hbalance]
  rw [← mul_sum]
  exact mul_div_mul_left _ _ hr

/-- Absolute shares require a capacity-utilization premise in addition to
bounded backlog. -/
theorem full_utilization_share (demand service : I → ℝ) (rate : ℝ)
    (hbalance : ∀ i, service i = rate*demand i)
    (hfull : ∑ i, service i = 1) (i : I) :
    service i = demand i / (∑ j, demand j) := by
  have hr : rate ≠ 0 := by
    intro hz
    simp [hbalance, hz] at hfull
  have h := normalized_share demand service rate hbalance hr i
  rwa [hfull, div_one] at h

/-- Address workload is separated into temporal and spatial work, so the
clock is part of the address cost, not an additional denominator term. -/
def workload (η : ℝ) : Fin 4 → ℝ := ![43, 3*43, 16*η, 5]

theorem workload_sum (η : ℝ) : (∑ i, workload η i) = 172+16*η+5 := by
  simp [workload, Fin.sum_univ_succ]
  ring

theorem persistent_clock_share (η rate : ℝ) (service : Fin 4 → ℝ)
    (q : Fin 4 → ℕ → ℝ) (C : Fin 4 → ℝ) (hr : rate ≠ 0)
    (hstep : ∀ i n, q i (n+1) = q i n + rate*workload η i-service i)
    (hbounded : ∀ i n, 0 ≤ q i n ∧ q i n ≤ C i) :
    service 0 / (∑ i, service i) = 43/(172+16*η+5) := by
  have hb := persistent_service (workload η) service rate q C hstep hbounded
  have h := normalized_share (workload η) service rate hb hr 0
  rw [workload_sum] at h
  exact h

theorem baseline_clock_share (rate : ℝ) (service : Fin 4 → ℝ)
    (q : Fin 4 → ℕ → ℝ) (C : Fin 4 → ℝ) (hr : rate ≠ 0)
    (hstep : ∀ i n, q i (n+1) = q i n + rate*workload overhead i-service i)
    (hbounded : ∀ i n, 0 ≤ q i n ∧ q i n ≤ C i) :
    service 0 / (∑ i, service i) = clockRatio := by
  simpa [clockRatio, footprint] using
    persistent_clock_share overhead rate service q C hr hstep hbounded

omit [Fintype I] in
/-- Any constant rate with matching service gives bounded constant queues.
Thus the persistence test itself does not select a unique absolute rate. -/
theorem balanced_queues_exist (demand : I → ℝ) (rate : ℝ) :
    ∃ (service : I → ℝ) (q : I → ℕ → ℝ),
      (∀ i n, q i (n+1) = q i n + rate*demand i-service i) ∧
      (∀ i n, 0 ≤ q i n ∧ q i n ≤ 1) := by
  refine ⟨fun i => rate*demand i, fun _ _ => 0, ?_, ?_⟩
  · intro i n; ring
  · intro i n; norm_num

end PMConstants.SteadyAllocation
