import PMConstants.Partition
import PMSubstrate.Research.SamplingDynamics

/-!
# A finite scheduling witness and its quantization limit

Multiplying the stated workload by 43 gives integer counts
`1849 + 5547 + 684 + 215 = 8295`. A reversible full-cycle scheduler realizes
the weak fraction as an equal-tick event frequency on these labels.

Such a frequency cannot be counted on just 43 equally weighted ticks. This
does not refute a weighted-cost ratio or a nonuniform/stochastic model; it
identifies the memory/period obligation for the uniform-event interpretation.
-/

noncomputable section
namespace PMConstants.FiniteService
open Finset

abbrev Slots := Fin 1849 ⊕ (Fin 5547 ⊕ (Fin 684 ⊕ Fin 215))

def clockEvent : Finset Slots := univ.map ⟨Sum.inl, Sum.inl_injective⟩

theorem slot_count : Fintype.card Slots = 8295 := by simp [Slots]

theorem clock_count : clockEvent.card = 1849 := by simp [clockEvent]

theorem scaled_workload :
    43 * (43 : ℚ) = 1849 ∧ 43 * (3*43 : ℚ) = 5547 ∧
      43 * (16*(171/172) : ℚ) = 684 ∧ 43 * (5 : ℚ) = 215 := by norm_num

theorem frequency_matches_ratio : ((1849 : ℚ)/8295 : ℝ) = clockRatio := by
  norm_num [clockRatio, footprint, overhead]

/-- A concrete finite label space with a full reversible orbit realizes the
ratio. The physical choice of this update and unit-duration clock is open. -/
theorem finite_cycle_realizes :
    ∃ orbit : Fin (Fintype.card Slots) ≃ Slots,
      PMSubstrate.SamplingDynamics.frequency
        (fun t : Fin (Fintype.card Slots) =>
          ((PMSubstrate.SamplingDynamics.orbitAdvance orbit)^[t.val]) (orbit 0))
        clockEvent = 1849/8295 := by
  have : NeZero (Fintype.card Slots) := ⟨Fintype.card_ne_zero⟩
  refine ⟨(Fintype.equivFin Slots).symm, ?_⟩
  rw [PMSubstrate.SamplingDynamics.actual_clock_frequency, clock_count, slot_count]
  norm_num

theorem weak_period_divisibility (k N : ℕ) (hN : N ≠ 0)
    (hf : (k : ℚ)/N = 1849/8295) : 8295 ∣ N :=
  PMSubstrate.SamplingDynamics.event_denominator_divides k N 1849 8295 hN
    (by decide) (by decide) hf

theorem one_clock_cannot_count_weak (k : ℕ) : (k : ℚ)/43 ≠ 1849/8295 := by
  intro hf
  have h := weak_period_divisibility k 43 (by decide) hf
  norm_num at h

/-- If the same equal-tick schedule must also contain whole 43-tick cycles,
its total period is a multiple of 356685. This is conditional scheduling
arithmetic, not a lower bound on the vacuum's Hilbert-space dimension. -/
theorem clock_compatible_period (k N : ℕ) (hN : N ≠ 0) (hclock : 43 ∣ N)
    (hf : (k : ℚ)/N = 1849/8295) : 356685 ∣ N := by
  have h := Nat.lcm_dvd hclock (weak_period_divisibility k N hN hf)
  have he : Nat.lcm 43 8295 = 356685 := by decide
  rwa [he] at h

end PMConstants.FiniteService
