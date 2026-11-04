import Mathlib.Tactic
import PMSubstrate.Impedance

/-! Conditional arithmetic of the paper's partition rules, with no empirical identification. -/
noncomputable section
namespace PMConstants

def overhead : ℝ := 171/172

def strongCoupling (α : ℝ) : ℝ := (16*overhead + 1/4)*α

def footprint : ℝ := 172 + 16*overhead + 5

def clockRatio : ℝ := 43/footprint

def selfCoupling : ℝ := (3-1/43)/23

def scalarToll : ℝ := 2*selfCoupling

def beta0 (nf : ℕ) : ℝ := 11 - 2/3*nf

def residual (α : ℝ) : ℝ := 16 - 2/3 - α

theorem exact_partition_values :
    overhead = 171/172 ∧ footprint = 8295/43 ∧ clockRatio = 1849/8295 ∧
    selfCoupling = 128/989 ∧ scalarToll = 256/989 := by
  norm_num [overhead, footprint, clockRatio, selfCoupling, scalarToll]

theorem overhead_bounds : 0 < overhead ∧ overhead < 1 := by norm_num [overhead]

theorem clock_ratio_bounds : 0 < clockRatio ∧ clockRatio < 1 := by
  norm_num [clockRatio, footprint, overhead]

theorem self_coupling_pos : 0 < selfCoupling := by norm_num [selfCoupling]

theorem beta_positive_iff (nf : ℕ) : 0 < beta0 nf ↔ nf ≤ 16 := by
  simp only [beta0]
  constructor
  · intro h
    by_contra hn
    have h17 : (17 : ℝ) ≤ nf := by exact_mod_cast (show 17 ≤ nf by omega)
    linarith
  · intro hn
    have hr : (nf : ℝ) ≤ 16 := by exact_mod_cast hn
    linarith

theorem residual_solvent (α : ℝ) : residual α + 2/3 + α = 16 := by
  unfold residual
  ring

theorem residual_bounds {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    14 < residual α ∧ residual α < 16 := by
  unfold residual
  constructor <;> linarith

/-- Solvency does not determine a unique allocation, even if all allocations are positive. -/
theorem solvency_not_unique :
    (14 : ℝ)+1+1 = 16 ∧ (13 : ℝ)+2+1 = 16 ∧
      ((14,1,1) : ℝ×ℝ×ℝ) ≠ (13,2,1) := by norm_num

/-- Paper 3's Toll formula is exactly paper 1's baseline Toll. -/
theorem inherited_toll :
    (1/(32 : ℝ)^3) * (2/5) * (1-5/172) = PMSubstrate.tollTerm PMSubstrate.baseline := by
  norm_num [PMSubstrate.tollTerm, PMSubstrate.baseline, PMSubstrate.Parameters.nodeCapacity,
    PMSubstrate.Parameters.resolution]

/-- With equal per-degree costs, the scalar mass relation is an algebraic identity. -/
theorem scalar_mass_consistency (v : ℝ) :
    (scalarToll/2)*v^2 = selfCoupling*v^2 := by
  unfold scalarToll
  ring

end PMConstants
