import PMCosmology.InformationCapacity
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Thermodynamic consistency conditional on area/entropy and energy laws.
No black-hole metric, Hawking state, radiation mechanism or entropy coefficient
is selected by these identities. The comparison uses G=ℏ=c=k_B=1. -/
noncomputable section
namespace PMCosmology.Thermodynamics

/-- A supplied entropy coefficient and quadratic mass-area relation. -/
def entropy (coefficient M : ℝ) : ℝ := coefficient*M^2

theorem entropy_derivative (coefficient M : ℝ) :
    HasDerivAt (entropy coefficient) (2*coefficient*M) M := by
  change HasDerivAt (fun x : ℝ => coefficient*x^2) (2*coefficient*M) M
  have h := ((hasDerivAt_id M).pow 2).const_mul coefficient
  change HasDerivAt (fun x : ℝ => coefficient*x^2) (coefficient*(2*M^1*1)) M at h
  have he : coefficient*(2*M^1*1) = 2*coefficient*M := by ring
  rw [he] at h
  exact h

/-- With E=M, the first law fixes T once S(M) has been supplied. -/
theorem first_law_temperature (coefficient M T : ℝ) (hc : coefficient ≠ 0) (hM : M ≠ 0) :
    T*(2*coefficient*M)=1 ↔ T=1/(2*coefficient*M) := by
  have hd : 2*coefficient*M ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hc) hM
  exact (eq_div_iff hd).symm

/-- Supplied A=16πM² and S=A/4 give S=4πM². This supplies the geometry
and normalization; D=4 alone does not prove either premise. -/
theorem area_entropy (M : ℝ) : (16*Real.pi*M^2)/4=entropy (4*Real.pi) M := by
  unfold entropy
  ring

/-- The familiar 8π follows from differentiating the supplied entropy, then
using the first law, rather than multiplying geometric labels. -/
theorem hawking_comparison (M T : ℝ) (hM : 0 < M) :
    T*(2*(4*Real.pi)*M)=1 ↔ T=1/(8*Real.pi*M) := by
  have he : 2*(4*Real.pi)*M = 8*Real.pi*M := by ring
  rw [← he]
  exact first_law_temperature (4*Real.pi) M T (by positivity) hM.ne'

/-- Larger M has smaller T in this conditional comparison model. -/
theorem temperature_decreases (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    1/(8*Real.pi*b) < 1/(8*Real.pi*a) := by
  apply one_div_lt_one_div_of_lt (by positivity)
  exact mul_lt_mul_of_pos_left hab (by positivity)

/-- The required cell area for the entropy coefficient 1/(4l²) depends on
log(q). Binary cells of area 4l² do not give that coefficient in nats. -/
theorem cell_area_normalization (cells q : ℕ) (l : ℝ) (hl : l ≠ 0) :
    InformationCapacity.information cells q =
      ((cells : ℝ)*(4*l^2*Real.log q))/(4*l^2) := by
  rw [InformationCapacity.information_adds]
  field_simp

end PMCosmology.Thermodynamics
