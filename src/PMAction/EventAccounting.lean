import PMSubstrate.NetCost
import Mathlib.Tactic

/-! Weighted finite-event accounting. The event law is supplied; linearity
neither requires independence nor selects that law. Uniform sampling recovers Paper I. -/
noncomputable section
namespace PMAction.EventAccounting
open Finset
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def eventWeight (law : Ω → ℝ) (E : Finset Ω) : ℝ := ∑ ω ∈ E, law ω

def cost (toll : ℝ) (law : Ω → ℝ) {n : ℕ} (E : Fin n → Finset Ω) : ℝ :=
  ∑ ω, law ω*(toll*∑ i, if ω ∈ E i then (1 : ℝ) else 0)

/-- One common primitive toll, with each event counted exactly once. -/
theorem weighted_linear (toll : ℝ) (law : Ω → ℝ) {n : ℕ} (E : Fin n → Finset Ω) :
    cost toll law E=toll*∑ i, eventWeight law (E i) := by
  calc
    cost toll law E = ∑ i, toll*∑ ω, if ω ∈ E i then law ω else 0 := by
      unfold cost
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro ω _
      split_ifs <;> simp_all; ring
    _ = ∑ i, toll*eventWeight law (E i) := by
      apply sum_congr rfl
      intro i _
      congr 1
      rw [← sum_filter]
      simp [eventWeight]
    _ = toll*∑ i, eventWeight law (E i) := (mul_sum _ _ _).symm

omit [DecidableEq Ω] in
/-- The weight of a uniformly sampled event is the substrate probability. -/
theorem uniform_eventWeight (E : Finset Ω) :
    eventWeight (fun _ => 1 / (Fintype.card Ω : ℝ)) E = PMSubstrate.NetCost.prob E := by
  simp [eventWeight, PMSubstrate.NetCost.prob,
    PMSubstrate.PersistenceEvents.uniformEventProbability, nsmul_eq_mul, div_eq_mul_inv]

/-- Uniform sampling specializes the weighted account to the substrate cost. -/
theorem uniform_recovers_netCost (toll : ℝ) {n : ℕ} (E : Fin n → Finset Ω) :
    cost toll (fun _ => 1/(Fintype.card Ω : ℝ)) E=PMSubstrate.NetCost.expectedCost toll E := by
  rw [weighted_linear, PMSubstrate.NetCost.expected_count_linear]
  simp only [uniform_eventWeight]

def binaryPMF (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

theorem binary_normalized (p : ℝ) : (∑ b, binaryPMF p b)=1 := by
  simp [binaryPMF]

theorem binary_nonnegative {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : ∀ b, 0 ≤ binaryPMF p b := by
  intro b; cases b <;> simp [binaryPMF] <;> linarith

/-- An explicit binary event, not a cost defined directly as a curvature score. -/
theorem binary_flag_cost (toll p : ℝ) :
    cost toll (binaryPMF p) (fun _ : Fin 1 => ({true} : Finset Bool))=toll*p := by
  rw [weighted_linear]
  simp [eventWeight, binaryPMF]

end PMAction.EventAccounting
