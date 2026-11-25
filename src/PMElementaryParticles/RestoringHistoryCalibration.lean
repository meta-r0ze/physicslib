import PMElementaryParticles.RestoringPulseCalibration
import PMKAutomaton.RestoringRingToll

/-!
# From a conditioned restoring history to a principal pulse

Survival distinguishes the set of receiver flags charged to an event.
For the closed ring, billing the initial two visits and billing all visits
through the full return give opposite comparisons with the steady-node
weight. Matching a pulse's shifted current to either history readout
then transmits that distinction to its principal area.
-/

noncomputable section
namespace PMElementaryParticles.RestoringPulseCalibration

open PMConstants.HandoffAdmittance RestoringWallShift
open PMAction.CarrierRateFromAdmittance PMKAutomaton.RestoringRingHistory

/-- A shifted current of conductance `w` fixes the weight of the transferred
port. This uses the two incoherent input populations of the port readout. -/
theorem shifted_weight_of_current (θ : ℝ) (g : Fin 3) (a : Fin 8) {w : ℝ}
    (hm : ∀ l r : ℝ, shiftedOutflow θ g a l r - l = w * (r - l)) :
    Complex.normSq (classPulse θ (.inr (g + 1, a)) (.inl (g, a))) = w := by
  apply through_eq_conductance
  intro l r
  rw [← shiftedOutflow_eq, hm]

/-- If the history weight is read as the shifted current, its principal
pulse area is fixed. The elapsed time is a separate input to the rate. -/
theorem principal_area_of_history_current {θ w : ℝ} (g : Fin 3) (a : Fin 8)
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2))
    (hm : ∀ l r : ℝ, shiftedOutflow θ g a l r - l = w * (r - l)) :
    θ = area w := by
  have hw := shifted_weight_of_current θ g a hm
  rw [classPulse_weight] at hw
  exact area_of_transfer hθ.1 hθ.2 hw

/-- The history-current calibration feeds the restoring/direct coefficient
at the elapsed durations of the individual pulses. -/
theorem rate_ratio_of_history_current (g : Fin 3) (a : Fin 8)
    {θ direct moveTime directTime w : ℝ}
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) (hd : direct ∈ Set.Icc 0 (Real.pi / 2))
    (hm : 0 < moveTime) (hdt : 0 < directTime)
    (hCurrent : ∀ l r : ℝ, shiftedOutflow θ g a l r - l = w * (r - l))
    (hcertain : Real.sin direct ^ 2 = 1) :
    (θ / moveTime) / (direct / directTime) =
      (2 * area w / Real.pi) * (directTime / moveTime) :=
  classPulse_rate_ratio g a hθ.1 hθ.2 hd.1 hd.2 hm hdt
    (shifted_weight_of_current θ g a hCurrent) hcertain

private theorem area_lt_of_weight_lt {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) :
    area u < area v := by
  unfold area
  exact Real.arcsin_lt_arcsin (by linarith [Real.sqrt_nonneg u]) (Real.sqrt_lt_sqrt hu huv)
    (Real.sqrt_le_one.mpr hv)

/-- At unit hazard, under a uniform prior on the same independent request
seeds and the indicated current matches, the two receiver accounts
bracket the steady-node principal area. This identifies the area ordering
even when the actual pulses have different elapsed durations. -/
theorem independent_history_area_bracket (either : Bool) (g : Fin 3) (a : Fin 8)
    {cycle visits : ℝ}
    (hc : cycle ∈ Set.Icc 0 (Real.pi / 2)) (hv : visits ∈ Set.Icc 0 (Real.pi / 2))
    (hCycle : ∀ l r : ℝ, shiftedOutflow cycle g a l r - l =
      cycleExitShare either (id : History → History) 1 * (r - l))
    (hVisits : ∀ l r : ℝ, shiftedOutflow visits g a l r - l =
      exitShare either (id : History → History) (visitToll either) 1 * (r - l)) :
    cycle < area (PMSubstrate.causalCoupling / 2) ∧
      area (PMSubstrate.causalCoupling / 2) < visits := by
  rw [principal_area_of_history_current g a hc hCycle,
    principal_area_of_history_current g a hv hVisits]
  have hAlpha := PMSubstrate.causalCoupling_bounds
  have hCycleWeight := exit_share_mem_Icc either (id : History → History)
    (fun q => receiverToll either q (2 * PMAction.Delta)) 1
  have hVisitsWeight := exit_share_mem_Icc either (id : History → History) (visitToll either) 1
  exact ⟨area_lt_of_weight_lt hCycleWeight.1 (unit_cycle_shares_lt_steady either).1 (by linarith [hAlpha.2]),
    area_lt_of_weight_lt (by linarith [hAlpha.1]) (steady_lt_unit_visit_shares either).1 hVisitsWeight.2⟩

end PMElementaryParticles.RestoringPulseCalibration
