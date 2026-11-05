import PMConstants.WorkloadLedger
import PMSubstrate.NetCost

/-!
# Primitive transition tolls versus composite operation costs

Paper I charges a common toll for each specified primitive transition event.
A macro operation realized by m such events costs m tolls. These lemmas connect
that event convention to Paper III's explicit availability ledger without
assuming that three distinct macro operation classes have equal lengths.
The availability sample and event realization remain supplied model data.
-/
noncomputable section
namespace PMConstants.TransitionLedger
open Finset
open PMConstants.WorkloadLedger

abbrev Sample := Fin 172

def available : Finset Sample := univ.erase 0

theorem available_probability : PMSubstrate.NetCost.prob available = overhead := by
  norm_num [PMSubstrate.NetCost.prob, available, overhead]

/-- An always-occurring macro operation with m primitive transitions. -/
def macroCost (c : ℝ) (m : ℕ) : ℝ :=
  PMSubstrate.NetCost.expectedCost c (fun _ : Fin m => (univ : Finset Sample))

/-- The same m primitive events, all gated by the specified availability event. -/
def gatedCost (c : ℝ) (m : ℕ) : ℝ :=
  PMSubstrate.NetCost.expectedCost c (fun _ : Fin m => available)

theorem macro_cost (c : ℝ) (m : ℕ) : macroCost c m = c*m := by
  rw [macroCost, PMSubstrate.NetCost.expected_count_linear]
  simp [PMSubstrate.NetCost.prob]

theorem gated_cost (c : ℝ) (m : ℕ) : gatedCost c m = c*m*overhead := by
  rw [gatedCost, PMSubstrate.NetCost.expected_count_linear]
  simp only [available_probability, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- No independence assumption is required by linearity of expectation. -/
def expectedLedger (c : ℝ) (address payload bus : ℕ) : ℝ :=
  172*macroCost c address + 16*gatedCost c payload + 5*macroCost c bus

theorem expected_ledger (c : ℝ) (address payload bus : ℕ) :
    expectedLedger c address payload bus =
      c * meanWorkload address payload bus := by
  rw [expectedLedger, macro_cost, gated_cost, macro_cost, mean_workload]
  ring

def clockShare (c : ℝ) (address payload bus : ℕ) : ℝ :=
  (43*macroCost c address) / expectedLedger c address payload bus

theorem primitive_share (c : ℝ) (hc : c ≠ 0) (address payload bus : ℕ) :
    clockShare c address payload bus = aggregateClockShare address payload bus := by
  rw [clockShare, macro_cost, expected_ledger, mean_workload, aggregate_share]
  rw [show 43*(c*(address : ℝ)) = c*(43*address) by ring]
  exact mul_div_mul_left _ _ hc

/-- The baseline follows if all three macro operations consist of one event. -/
theorem single_transition_share (c : ℝ) (hc : c ≠ 0) :
    clockShare c 1 1 1 = clockRatio := by
  rw [primitive_share c hc]
  simpa only [Nat.cast_one, Nat.cast_ofNat] using aggregate_unit_share

/-- Common primitive tolls do not exclude a two-event payload operation. -/
theorem same_unit_toll_different_share : clockShare 1 1 2 1 ≠ clockShare 1 1 1 1 := by
  rw [primitive_share 1 (by norm_num), primitive_share 1 (by norm_num)]
  simpa only [Nat.cast_one, Nat.cast_ofNat] using relative_costs_change_share

/-- The one-transition realization is the least-cost positive-integer ledger.
This comparison is conditional on that realization being physically admissible. -/
theorem unit_ledger_lower_bound (address payload bus : ℕ)
    (hA : 0 < address) (hP : 0 < payload) (hB : 0 < bus) :
    footprint ≤ expectedLedger 1 address payload bus := by
  have ha : (1 : ℝ) ≤ address := by exact_mod_cast hA
  have hp : (1 : ℝ) ≤ payload := by exact_mod_cast hP
  have hb : (1 : ℝ) ≤ bus := by exact_mod_cast hB
  rw [expected_ledger, mean_workload]
  norm_num [footprint, overhead, one_mul, PMSubstrate.E8Values.RM_eq,
    PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.sigma_eq]
  linarith

/-- Attaining the lower bound forces all three operation lengths to be one. -/
theorem unit_ledger_equality_iff (address payload bus : ℕ)
    (hA : 0 < address) (hP : 0 < payload) (hB : 0 < bus) :
    expectedLedger 1 address payload bus = footprint ↔
      address = 1 ∧ payload = 1 ∧ bus = 1 := by
  have ha : (1 : ℝ) ≤ address := by exact_mod_cast hA
  have hp : (1 : ℝ) ≤ payload := by exact_mod_cast hP
  have hb : (1 : ℝ) ≤ bus := by exact_mod_cast hB
  constructor
  · intro h
    rw [expected_ledger, mean_workload] at h
    norm_num [footprint, overhead] at h
    have ea : (address : ℝ) = 1 := by linarith
    have ep : (payload : ℝ) = 1 := by linarith
    have eb : (bus : ℝ) = 1 := by linarith
    exact ⟨by exact_mod_cast ea, by exact_mod_cast ep, by exact_mod_cast eb⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rw [expected_ledger]
    simpa using unit_footprint

/-- Economy selects the proposed ratio if the single-transition baseline is
an admissible competitor and the selected realization is no more costly. -/
theorem economical_share (address payload bus : ℕ)
    (hA : 0 < address) (hP : 0 < payload) (hB : 0 < bus)
    (hbest : expectedLedger 1 address payload bus ≤ expectedLedger 1 1 1 1) :
    clockShare 1 address payload bus = clockRatio := by
  have hbase : expectedLedger 1 1 1 1 = footprint :=
    (unit_ledger_equality_iff 1 1 1 (by norm_num) (by norm_num) (by norm_num)).mpr
      ⟨rfl, rfl, rfl⟩
  rw [hbase] at hbest
  have he := le_antisymm hbest (unit_ledger_lower_bound address payload bus hA hP hB)
  obtain ⟨rfl, rfl, rfl⟩ := (unit_ledger_equality_iff address payload bus hA hP hB).mp he
  exact single_transition_share 1 (by norm_num)

/-- The four categories are temporal address, spatial address, payload and bus. -/
def demand (address payload bus : ℕ) : Fin 4 → ℝ :=
  ![43*address, 129*address, 16*overhead*payload, 5*bus]

theorem demand_sum (address payload bus : ℕ) :
    (∑ i, demand address payload bus i) = meanWorkload address payload bus := by
  simp [demand, Fin.sum_univ_succ, mean_workload]
  ring

/-- Positive weighted ledgers can all be sustained by bounded, capacity-limited
fluid queues. This is an accounting witness, not a microscopic E8 dynamics. -/
theorem persistent_queues (address payload bus : ℕ)
    (hA : 0 < address) (hP : 0 < payload) (hB : 0 < bus) :
    ∃ (rate : ℝ) (service : Fin 4 → ℝ) (q : Fin 4 → ℕ → ℝ),
      0 < rate ∧ (∀ i, 0 < service i) ∧ (∑ i, service i) = 1 ∧
      (∀ i n, q i (n+1) = q i n + rate*demand address payload bus i-service i) ∧
      (∀ i n, 0 ≤ q i n ∧ q i n ≤ 1) ∧
      service 0/(∑ i, service i) = aggregateClockShare address payload bus := by
  have hpos : ∀ i, 0 < demand address payload bus i := by
    intro i
    fin_cases i <;> simp [demand, overhead] <;> positivity
  have htotal : 0 < ∑ i, demand address payload bus i :=
    sum_pos (fun i _ => hpos i) (by simp)
  let total : ℝ := ∑ i, demand address payload bus i
  let rate : ℝ := 1/total
  let service : Fin 4 → ℝ := fun i => rate*demand address payload bus i
  have hr : 0 < rate := one_div_pos.mpr htotal
  have hs : (∑ i, service i) = 1 := by
    simp only [service, ← mul_sum]
    exact one_div_mul_cancel htotal.ne'
  refine ⟨rate, service, fun _ _ => 0, hr,
    fun i => mul_pos hr (hpos i), hs, ?_, ?_, ?_⟩
  · intro i n; dsimp [service]; ring
  · intro i n; norm_num
  · have hb : ∀ i, service i = rate*demand address payload bus i := fun _ => rfl
    rw [SteadyAllocation.normalized_share (demand address payload bus) service rate hb hr.ne' 0,
      demand_sum, mean_workload, aggregate_share]
    rfl

end PMConstants.TransitionLedger
