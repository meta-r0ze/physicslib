import PMConstants.ReferenceFrames
import PMConstants.SteadyAllocation
import PMConstants.RegulatoryBudget

/-!
# From specified resource processes to the allocation equations

The earlier `Allocation.Compatible` equations are consequences of this model:
mandatory in-band reference with maximal payload, persistent constant-rate queues
for the supplied workload, cyclic direction/clock credits, and maximal uniform
restoring gain. No observed coupling is used. The architecture, workload and
optimization objectives remain explicit; these are not consequences of the
unqualified assertion that some system persists.
-/

noncomputable section
namespace PMConstants.ResourceSelection
open Finset

def payloadFraction (R : Finset (Fin 172)) : ℝ := (univ \ R).card / 172

/-- A resource-process certificate. A different persistent architecture need
not have this resource ledger, reference mechanism or optimization objective. -/
structure Process where
  reserved : Finset (Fin 172)
  hasReference : reserved.Nonempty
  maximalPayload : ∀ S : Finset (Fin 172), S.Nonempty →
    (univ \ S).card ≤ (univ \ reserved).card
  rate : ℝ
  positiveRate : 0 < rate
  service : Fin 4 → ℝ
  capacity : ∑ i, service i ≤ 1
  backlog : Fin 4 → ℕ → ℝ
  bound : Fin 4 → ℝ
  update : ∀ i n, backlog i (n+1) = backlog i n +
    rate * SteadyAllocation.workload (payloadFraction reserved) i-service i
  persistent : ∀ i n, 0 ≤ backlog i n ∧ backlog i n ≤ bound i
  direction : Fin 4 → ℝ
  directionInvariant : ∀ i, direction (finRotate 4 i) = direction i
  directionTotal : ∑ i, direction i = 1
  clock : Fin 43 → ℝ
  clockInvariant : ∀ i, clock (finRotate 43 i) = clock i
  clockTotal : ∑ i, clock i = 1
  gain : ℝ
  maximalGain : RegulatoryBudget.Maximal 23 3 (clock 0) gain

/-- The values read off the process. Strong load is an additive count of
16 equal payload-channel loads plus one directional anchoring credit.
Multiplication by α is the stipulated conversion from load to coupling. -/
def values (p : Process) (α : ℝ) : Allocation.Values where
  η := payloadFraction p.reserved
  strong := ((∑ _i : Fin 16, payloadFraction p.reserved) + p.direction 0) * α
  weak := p.service 0 / (∑ i, p.service i)
  scalar := p.gain

theorem reference_forced (p : Process) : payloadFraction p.reserved = overhead :=
  ReferenceFrames.optimal_172_overhead p.reserved p.hasReference p.maximalPayload

theorem scalar_forced (p : Process) : p.gain = selfCoupling := by
  have hc := RegulatoryBudget.clock_credit p.clock p.clockInvariant p.clockTotal
  have hm := p.maximalGain
  rw [hc] at hm
  exact (RegulatoryBudget.scalar_maximal_iff _).mp hm

theorem weak_forced (p : Process) : p.service 0 / (∑ i, p.service i) = clockRatio := by
  have h := SteadyAllocation.persistent_clock_share (payloadFraction p.reserved)
    p.rate p.service p.backlog p.bound p.positiveRate.ne' p.update p.persistent
  rw [reference_forced p] at h
  simpa [clockRatio, footprint, overhead, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.RM_eq, PMSubstrate.E8Values.nu_eq,
    PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.overhead_eq] using h

/-- The process discharges each of the earlier bare allocation equations. -/
theorem process_compatible (p : Process) (α : ℝ) : Allocation.Compatible α (values p α) := by
  have ho := reference_forced p
  have hd := RegulatoryBudget.directional_credit p.direction
    p.directionInvariant p.directionTotal
  constructor
  · change 172 * payloadFraction p.reserved = 171
    rw [ho]; norm_num [overhead]
  · change ((∑ _i : Fin 16, payloadFraction p.reserved) + p.direction 0) * α = _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hd]
    rfl
  · change (172 + 16*payloadFraction p.reserved + 5) *
      (p.service 0 / ∑ i, p.service i) = 43
    rw [ho, weak_forced p]
    norm_num [overhead, clockRatio, footprint]
  · change 23*p.gain + 1/43 = 3
    rw [scalar_forced p]
    norm_num [selfCoupling]

theorem process_selects (p : Process) (α : ℝ) :
    (values p α).η = overhead ∧ (values p α).strong = strongCoupling α ∧
      (values p α).weak = clockRatio ∧ (values p α).scalar = selfCoupling :=
  Allocation.allocation_forced α (values p α) (process_compatible p α)

/-- Nonvacuity: an explicit, positive-rate finite-resource witness exists.
The continuous queues here are constant fluid queues, not a microscopic
finite-alphabet automaton. Clock and direction labels are finite. -/
def witness : Process where
  reserved := {0}
  hasReference := by simp
  maximalPayload := by
    intro S hS
    have h := ReferenceFrames.inband_bound S hS
    simpa [ReferenceFrames.payload_count] using h
  rate := 1/200
  positiveRate := by norm_num
  service := fun i => (1/200) * SteadyAllocation.workload (payloadFraction {0}) i
  capacity := by
    rw [← Finset.mul_sum, SteadyAllocation.workload_sum]
    norm_num [payloadFraction, ReferenceFrames.payload_count]
  backlog := fun _ _ => 0
  bound := fun _ => 1
  update := by intros; ring
  persistent := by intros; norm_num
  direction := fun _ => 1/4
  directionInvariant := by intros; rfl
  directionTotal := by norm_num
  clock := fun _ => 1/43
  clockInvariant := by intros; rfl
  clockTotal := by norm_num
  gain := selfCoupling
  maximalGain := (RegulatoryBudget.scalar_maximal_iff _).mpr rfl

theorem process_exists : Nonempty Process := ⟨witness⟩

end PMConstants.ResourceSelection
