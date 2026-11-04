import PMConstants.AvailabilityAudit
import PMConstants.WorkloadLedger

/-! Collision semantics can give the aggregate payload count along each single
43-cycle. Four targets per row suffice; uniform direction mixing and uniform
per-channel availability are not required. The target map and collision rule
remain operational premises. -/
noncomputable section
namespace PMConstants.BalancedAvailability
open Finset PMConstants.General.ReferenceCapacity PMConstants.AvailabilityAudit

def Balanced (tgt : Fin 16 → Grid) : Prop :=
  ∀ d : Fin 4, (univ.filter (fun j => (tgt j).1 = d)).card = 4

/-- Sampled executed payload work with the explicitly stipulated collision rule. -/
def executed (tgt : Fin 16 → Grid) (o : Grid) : ℝ :=
  ∑ j, if tgt j = o then 0 else 1

theorem executed_sum (tgt : Fin 16 → Grid) (o : Grid) :
    (∑ k : Fin 43, executed tgt (gridTick^[k.val] o)) =
      43*16 - ∑ j, hits o (tgt j) := by
  have heq : ∀ j : Fin 16, ∀ x : Grid,
      (if tgt j = x then (0 : ℝ) else 1) =
        1 - (if x = tgt j then 1 else 0) := by
    intro j x; by_cases h : tgt j = x
    · simp [h]
    · simp [h, Ne.symm h]
  unfold executed
  simp_rw [heq]
  rw [sum_comm]
  simp_rw [sum_sub_distrib]
  simp [hits]
  norm_num

theorem balanced_payload_mean (tgt : Fin 16 → Grid) (hb : Balanced tgt) (o : Grid) :
    (∑ k : Fin 43, executed tgt (gridTick^[k.val] o))/43 = 16*PMConstants.overhead := by
  have h := (collision_aggregate o tgt).mpr (hb o.1)
  rw [executed_sum]
  norm_num [PMConstants.overhead] at *
  linarith

/-- If all sixteen operations are genuinely required at every phase, simply
skipping four per cycle is not persistent finite-backlog service. The reduced
workload needs a reason why those operations are unnecessary or recovered. -/
theorem required_work_cannot_be_skipped (tgt : Fin 16 → Grid) (hb : Balanced tgt)
    (o : Grid) (q : ℕ → ℝ) (C : ℝ)
    (hstep : ∀ n, q (n+1) = q n + 43*16 -
      ∑ k : Fin 43, executed tgt (gridTick^[k.val] o))
    (hbounded : ∀ n, 0 ≤ q n ∧ q n ≤ C) : False := by
  have hm := balanced_payload_mean tgt hb o
  norm_num [PMConstants.overhead] at hm
  have hs : (∑ k : Fin 43, executed tgt (gridTick^[k.val] o)) = 684 := by linarith
  have hz := PMConstants.SteadyAllocation.bounded_drift_zero q 4 C
    (fun n => by rw [hstep, hs]; ring) hbounded
  norm_num at hz

/-- A concrete balanced injection exists. This is a combinatorial witness,
not a canonical map from the substrate channels to the register grid. -/
def productTargets (j : Fin 16) : Grid :=
  let dk := finProdFinEquiv.symm j
  (dk.1, Fin.castLE (by norm_num : 4 ≤ 43) dk.2)

theorem product_targets_balanced : Balanced productTargets := by
  unfold Balanced
  decide +kernel

theorem product_targets_injective : Function.Injective productTargets := by decide +kernel

def sampleWork (tgt : Fin 16 → Grid) (o : Grid) : ℝ := 172+5+executed tgt o

theorem balanced_mean_footprint (tgt : Fin 16 → Grid) (hb : Balanced tgt) (o : Grid) :
    (∑ k : Fin 43, sampleWork tgt (gridTick^[k.val] o))/43 = PMConstants.footprint := by
  have h := balanced_payload_mean tgt hb o
  unfold sampleWork
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold PMConstants.footprint
  linarith

/-- Normalize total clock work by total work, along any starting direction. -/
theorem balanced_aggregate_share (tgt : Fin 16 → Grid) (hb : Balanced tgt) (o : Grid) :
    (∑ _k : Fin 43, (43 : ℝ)) /
      (∑ k : Fin 43, sampleWork tgt (gridTick^[k.val] o)) = PMConstants.clockRatio := by
  have h := balanced_mean_footprint tgt hb o
  have hs : (∑ k : Fin 43, sampleWork tgt (gridTick^[k.val] o)) =
      43*PMConstants.footprint := by linarith
  rw [hs]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num only [Nat.cast_ofNat]
  norm_num [PMConstants.clockRatio, PMConstants.footprint, PMConstants.overhead]

end PMConstants.BalancedAvailability
