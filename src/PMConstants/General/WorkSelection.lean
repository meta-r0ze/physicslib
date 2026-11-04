import PMConstants.General.Service

/-! Persistence constrains service for supplied work; throughput optimization
then selects least work within the stated feasible family. Neither theorem
invents a physical demand vector or its primitive lower bounds. -/
namespace PMConstants.General.WorkSelection
open Finset
variable {I : Type*} [Fintype I]

/-- Unit service capacity, nonnegative service and bounded conserved queues.
These are fluid queues, not a constructed microscopic finite-state update. -/
def Feasible (d : I → ℝ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∃ (s : I → ℝ) (q : I → ℕ → ℝ) (C : I → ℝ),
    (∀ i, 0 ≤ s i) ∧ (∑ i, s i) ≤ 1 ∧
    (∀ i n, q i (n+1) = q i n + r*d i-s i) ∧
    (∀ i n, 0 ≤ q i n ∧ q i n ≤ C i)

theorem capacity_bound {d : I → ℝ} {r : ℝ} (h : Feasible d r) :
    r*(∑ i, d i) ≤ 1 := by
  obtain ⟨_,s,q,C,_,hs,hstep,hbound⟩ := h
  have he : ∀ i, s i=r*d i := by
    intro i
    have hz := Service.bounded_drift_zero (q i) (r*d i-s i) (C i)
      (fun n => by rw [hstep]; ring) (hbound i)
    linarith
  simpa only [he,← mul_sum] using hs

/-- Conversely a supplied nonnegative workload admits constant bounded queues
whenever its total demand fits. No required work is discarded. -/
theorem feasible_iff (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) (r : ℝ) :
    Feasible d r ↔ 0 ≤ r ∧ r*(∑ i, d i) ≤ 1 := by
  constructor
  · intro h; exact ⟨h.1,capacity_bound h⟩
  · rintro ⟨hr,hcap⟩
    refine ⟨hr,fun i => r*d i,fun _ _ => 0,fun _ => 0,
      fun i => mul_nonneg hr (hd i),?_,?_,?_⟩
    · simpa only [← mul_sum] using hcap
    · intro i n; ring
    · intro i n; exact ⟨le_refl _,le_refl _⟩

/-- An exact sustainable-rate optimum for specified positive total work. -/
theorem maximum_rate (d : I → ℝ) (hd : ∀ i, 0 ≤ d i)
    (ht : 0 < ∑ i, d i) :
    Feasible d (1/(∑ i, d i)) ∧
      ∀ r, Feasible d r → r ≤ 1/(∑ i, d i) := by
  constructor
  · apply (feasible_iff d hd _).mpr
    exact ⟨by positivity,by rw [one_div_mul_cancel ht.ne']⟩
  · intro r hr
    exact (le_div_iff₀ ht).mpr (capacity_bound hr)

end PMConstants.General.WorkSelection
