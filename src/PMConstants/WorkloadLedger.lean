import PMConstants.SteadyAllocation

/-!
# Before selecting a coupling: what does the workload average count?

A finite proposed operation ledger contains 172 address operations, 16 payload
operations and 5 bus operations. An availability trial suppresses the payload
class in one of 172 equally weighted cases. This is an explicit sample/readout
model, not a derived physical clock or the whole E8 state space.

It recovers the stated mean footprint at common unit cost. Relative costs of
different operation classes and the averaging/observation rule are additional
inputs. Mean per-trial fractions differ from the fraction of total work.
-/
noncomputable section
namespace PMConstants.WorkloadLedger
open Finset

abbrev Trial := Fin 172
abbrev Jobs := (Fin 4 × Fin 43) ⊕ (Fin 16 ⊕ Fin 5)

def charge (address payload bus : ℝ) (t : Trial) : Jobs → ℝ
  | .inl _ => address
  | .inr (.inl _) => if t = 0 then 0 else payload
  | .inr (.inr _) => bus

def workload (address payload bus : ℝ) (t : Trial) : ℝ :=
  ∑ job, charge address payload bus t job

theorem job_count : Fintype.card Jobs = 193 := by simp [Jobs]

theorem workload_formula (address payload bus : ℝ) (t : Trial) :
    workload address payload bus t = 172*address + 5*bus +
      if t = 0 then 0 else 16*payload := by
  simp [workload, charge, Jobs, Fintype.sum_sum_type]
  split_ifs <;> ring

theorem workload_sum (address payload bus : ℝ) :
    (∑ t, workload address payload bus t) =
      172*(172*address+5*bus)+171*16*payload := by
  simp_rw [workload_formula]
  have heq : ∀ t : Trial, (if t = 0 then 0 else 16*payload) =
      16*payload - (if t = 0 then 16*payload else 0) := by
    intro t; split_ifs <;> ring
  simp_rw [heq]
  rw [sum_add_distrib, sum_sub_distrib]
  simp [Trial]
  ring

def meanWorkload (address payload bus : ℝ) : ℝ :=
  (∑ t, workload address payload bus t)/172

theorem mean_workload (address payload bus : ℝ) :
    meanWorkload address payload bus = 172*address+16*overhead*payload+5*bus := by
  rw [meanWorkload, workload_sum]
  norm_num [overhead]
  ring

theorem unit_workload (t : Trial) : workload 1 1 1 t = if t = 0 then 177 else 193 := by
  rw [workload_formula]
  split_ifs <;> norm_num

theorem unit_footprint : meanWorkload 1 1 1 = footprint := by
  rw [mean_workload]
  unfold footprint
  ring

/-- The coefficient selected by counting all clock work against all work. -/
def aggregateClockShare (address payload bus : ℝ) : ℝ :=
  (∑ _t : Trial, 43*address) / ∑ t, workload address payload bus t

theorem aggregate_share (address payload bus : ℝ) :
    aggregateClockShare address payload bus =
      43*address/(172*address+16*overhead*payload+5*bus) := by
  unfold aggregateClockShare
  rw [workload_sum]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show 172*(172*address+5*bus)+171*16*payload =
    172*(172*address+16*overhead*payload+5*bus) by
      norm_num [overhead]; ring]
  norm_num only [Nat.cast_ofNat]
  exact mul_div_mul_left _ _ (by norm_num : (172 : ℝ) ≠ 0)

theorem aggregate_unit_share : aggregateClockShare 1 1 1 = clockRatio := by
  rw [aggregate_share]
  unfold clockRatio footprint
  norm_num

/-- Within-class homogeneity leaves these relative operation tolls open. -/
theorem relative_costs_change_share :
    aggregateClockShare 1 2 1 ≠ aggregateClockShare 1 1 1 := by
  rw [aggregate_share, aggregate_share]
  norm_num [overhead]

/-- A common unit rescaling cancels. Relative class costs do not. -/
theorem common_unit_invariant (address payload bus c : ℝ) (hc : c ≠ 0) :
    aggregateClockShare (c*address) (c*payload) (c*bus) =
      aggregateClockShare address payload bus := by
  rw [aggregate_share, aggregate_share]
  rw [show 172*(c*address)+16*overhead*(c*payload)+5*(c*bus) =
    c*(172*address+16*overhead*payload+5*bus) by ring,
    show 43*(c*address) = c*(43*address) by ring]
  exact mul_div_mul_left _ _ hc

/-- This is a different observation: give each availability trial equal
weight, normalize inside the trial, then average the resulting fractions. -/
def meanClockShare : ℝ := (∑ t : Trial, 43/workload 1 1 1 t)/172

theorem mean_trial_share : meanClockShare = (7615 : ℝ)/34161 := by
  have heq : ∀ t : Trial, 43/workload 1 1 1 t =
      43/193 + (if t = 0 then 43/177-43/193 else 0) := by
    intro t
    rw [unit_workload]
    split_ifs <;> norm_num
  unfold meanClockShare
  simp_rw [heq]
  rw [sum_add_distrib]
  simp [Trial]
  norm_num

theorem averaging_order_matters : aggregateClockShare 1 1 1 < meanClockShare := by
  rw [aggregate_unit_share, mean_trial_share]
  norm_num [clockRatio, footprint, overhead]

end PMConstants.WorkloadLedger
