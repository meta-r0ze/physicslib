import PMConstants.BalancedAvailability
import PMConstants.General.Service

/-! Allocation from cycle totals of the balanced collision model.
This removes constant per-phase work and per-channel eta assumptions from the
queue argument. Collision semantics, balanced targets, equal operation units,
a common rate and the observable defined by total service remain model inputs.
-/
noncomputable section
namespace PMConstants.PeriodicAllocation
open Finset PMConstants.General.ReferenceCapacity PMConstants.BalancedAvailability

/-- Clock, spatial address, executed payload and bus operation demands. -/
def demand (tgt : Fin 16 → Grid) (o : Grid) (i : Fin 4) (t : Fin PMSubstrate.E8Values.Delta) : ℝ :=
  ![43, 129, executed tgt ((gridTick^[t.val]) o), 5] i

theorem cycle_demand (tgt : Fin 16 → Grid) (hb : Balanced tgt) (o : Grid) (i : Fin 4) :
    (∑ t, demand tgt o i t) = 43*SteadyAllocation.workload overhead i := by
  have hp := balanced_payload_mean tgt hb o
  fin_cases i <;> simp [demand, SteadyAllocation.workload] <;> linarith

/-- Repeated-cycle persistence fixes total service ratios despite fluctuations
inside the cycle. The phase-only update may remain in any one direction row. -/
theorem persistent_clock_share (tgt : Fin 16 → Grid) (hb : Balanced tgt) (o : Grid)
    (q : Fin 4 → ℕ → Fin 44 → ℝ) (service : Fin 4 → Fin PMSubstrate.E8Values.Delta → ℝ)
    (rate : ℝ) (C : Fin 4 → ℝ) (hr : rate ≠ 0)
    (hstep : ∀ i n t, q i n t.succ = q i n t.castSucc + rate*demand tgt o i t-service i t)
    (hlink : ∀ i n, q i (n+1) 0 = q i n (Fin.last 43))
    (hbounded : ∀ i n, 0 ≤ q i n 0 ∧ q i n 0 ≤ C i) :
    (∑ t, service 0 t)/(∑ i, ∑ t, service i t) = clockRatio := by
  rw [General.Service.normalized_cycle_share q (demand tgt o) service rate C hr
    hstep hlink hbounded 0]
  simp_rw [cycle_demand tgt hb o]
  rw [← mul_sum]
  rw [mul_div_mul_left _ _ (by norm_num : (43 : ℝ) ≠ 0)]
  rw [SteadyAllocation.workload_sum]
  rfl

end PMConstants.PeriodicAllocation
