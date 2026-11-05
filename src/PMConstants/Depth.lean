import PMConstants.Partition
import PMSubstrate.E8Values
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt

noncomputable section
namespace PMConstants.Depth

/-- This is the attenuation law stipulated by the paper, with the half-period
written as `Delta/chi`. -/
def gravity (α : ℝ) : ℝ := residual α *
  α ^ ((PMSubstrate.E8Values.Delta : ℝ)/(PMSubstrate.E8Values.chi : ℝ))

def planck (me g : ℝ) : ℝ := me / Real.sqrt g

def impedance (me g m : ℝ) : ℝ := me / (m*Real.sqrt g)

/-- A per-hop survival probability 1-α gives a different law from α^r. -/
theorem attenuation_laws_differ {α r : ℝ} (h0 : 0 < α) (hhalf : α < 1/2)
    (hr : 0 < r) : α^r < (1-α)^r := by
  exact Real.rpow_lt_rpow (le_of_lt h0) (by linarith) hr

theorem gravity_pos {α : ℝ} (h0 : 0 < α) (h1 : α < 1) : 0 < gravity α := by
  exact mul_pos (by linarith [(residual_bounds h0 h1).1]) (Real.rpow_pos_of_pos h0 _)

theorem planck_pos {me g : ℝ} (hm : 0 < me) (hg : 0 < g) : 0 < planck me g :=
  div_pos hm (Real.sqrt_pos.mpr hg)

theorem impedance_ratio (me g m : ℝ) : impedance me g m = planck me g / m := by
  unfold impedance planck
  rw [div_div, mul_comm]

theorem unity_at_planck {me g : ℝ} (hm : 0 < me) (hg : 0 < g) :
    impedance me g (planck me g) = 1 := by
  rw [impedance_ratio]
  exact div_self (ne_of_gt (planck_pos hm hg))

theorem unity_iff {me g m : ℝ} (_hme : 0 < me) (_hg : 0 < g) (hm : 0 < m) :
    impedance me g m = 1 ↔ m = planck me g := by
  rw [impedance_ratio, div_eq_one_iff_eq (ne_of_gt hm)]
  exact eq_comm

/-- For the displayed Z_G(m), the impedance is greater than one below M_P. -/
theorem below_planck_impedance_gt_one {me g m : ℝ} (hm : 0 < m) :
    1 < impedance me g m ↔ m < planck me g := by
  rw [impedance_ratio, lt_div_iff₀ hm]
  simp

theorem electron_planck_relation {me g : ℝ} (hme : 0 < me) (hg : 0 < g) :
    (me / planck me g)^2 = g := by
  have hs : Real.sqrt g ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hg)
  have he : me ≠ 0 := ne_of_gt hme
  have hr : me / planck me g = Real.sqrt g := by
    unfold planck
    field_simp
  rw [hr, Real.sq_sqrt (le_of_lt hg)]

end PMConstants.Depth
