import PMCosmology.Scaling
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Consequences of the stipulated local capacity law. These are local index
and clock-speed identities, not a metric, an event horizon, or an exterior-field
solution. In particular a local convexity result is not Birkhoff violation. -/
noncomputable section
namespace PMCosmology.Saturation

/-- Residual-capacity clock speed, extended continuously to saturation.
Unlike division by the index, this expression is well behaved at K=C. -/
def speed (c C K : ℝ) : ℝ := c * (C-K) / C

theorem speed_at_capacity (c C : ℝ) : speed c C C = 0 := by simp [speed]

theorem speed_bounds (c C K : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hK : 0 ≤ K) (hKC : K < C) : 0 < speed c C K ∧ speed c C K ≤ c := by
  unfold speed
  constructor
  · exact div_pos (mul_pos hc (sub_pos.mpr hKC)) hC
  · apply (div_le_iff₀ hC).mpr
    nlinarith

/-- Inverse-index interpretation is valid below saturation, where n≠0. -/
theorem inverse_index (c C K : ℝ) (hC : C ≠ 0) (hKC : K ≠ C) :
    c / refractiveIndex C K = speed c C K := by
  unfold refractiveIndex speed
  field_simp

/-- Exact weak-load expansion with the nonnegative quadratic remainder exposed. -/
theorem weak_load_remainder (C K : ℝ) (hC : C ≠ 0) (hKC : K ≠ C) :
    refractiveIndex C K - (1+K/C) = K^2/(C*(C-K)) := by
  unfold refractiveIndex
  have hd : C-K ≠ 0 := sub_ne_zero.mpr (Ne.symm hKC)
  field_simp
  ring

/-- Equal mean occupancy need not give equal mean local index. -/
theorem mean_index_gap (C a b : ℝ) (ha : a < C) (hb : b < C) :
    (refractiveIndex C a + refractiveIndex C b)/2 - refractiveIndex C ((a+b)/2) =
      C*(a-b)^2/(2*(C-a)*(C-b)*(2*C-a-b)) := by
  have h1 : C-a ≠ 0 := by linarith
  have h2 : C-b ≠ 0 := by linarith
  have h3 : C-(a+b)/2 ≠ 0 := by linarith
  have h4 : 2*C-a-b ≠ 0 := by linarith
  have h5 : C*2-b-a ≠ 0 := by linarith
  unfold refractiveIndex
  field_simp [h1, h2, h3, h4, h5]
  ring_nf
  field_simp [h5]
  ring

theorem mean_index_strict (C a b : ℝ) (hC : 0 < C) (ha : a < C)
    (hb : b < C) (hab : a ≠ b) :
    refractiveIndex C ((a+b)/2) < (refractiveIndex C a + refractiveIndex C b)/2 := by
  have h := mean_index_gap C a b ha hb
  have hn : 0 < C*(a-b)^2 := mul_pos hC (sq_pos_of_ne_zero (sub_ne_zero.mpr hab))
  have hd : 0 < 2*(C-a)*(C-b)*(2*C-a-b) := by
    have h1 : 0 < C-a := by linarith
    have h2 : 0 < C-b := by linarith
    have h3 : 0 < 2*C-a-b := by linarith
    positivity
  have := div_pos hn hd
  linarith

/-- The speed has an ordinary finite limit even though the index diverges. -/
theorem speed_tendsto (c C : ℝ) :
    Filter.Tendsto (speed c C) (nhds C) (nhds 0) := by
  have h : Continuous (speed c C) := by unfold speed; fun_prop
  simpa only [speed_at_capacity] using h.continuousAt.tendsto (x := C)

end PMCosmology.Saturation
