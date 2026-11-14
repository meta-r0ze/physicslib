import PMAction.FiniteVertex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! Scalar link polarization for a straight, Abelian link with a line-averaged
plane-wave probe. The single-link phase response is sinc-weighted. The mixed
second variation below pairs opposite external momenta (the two line averages
give the same real sinc factor). The longitudinal loop identity keeps the
translation difference, which matters on a cut momentum shell. -/
noncomputable section
namespace PMAction.PolarizationContact
open Real D4Gauge LeadingLog FiniteVertex

abbrev Momentum := Fin 4 → ℝ

/-- Mixed second variation of the cosine link for two additive phase probes. -/
theorem link_second_variation (x u v : ℝ) :
    HasDerivAt (fun s => deriv (fun t => 1 - cos (x + s * u + t * v)) 0)
      (cos x * u * v) 0 := by
  have first (s : ℝ) :
      deriv (fun t => 1 - cos (x + s * u + t * v)) 0 = sin (x + s * u) * v := by
    have h : HasDerivAt (fun t : ℝ => x + s * u + t * v) v 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).mul_const v).const_add (x + s * u))
    rw [(h.cos.const_sub 1).deriv]
    simp
  simp_rw [first]
  have h : HasDerivAt (fun s : ℝ => x + s * u) u 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const u).const_add x)
  simpa [mul_assoc] using (h.sin.mul_const v)

/-- Centered finite-momentum vertex contracted with a probe direction. -/
def leg (a : ℝ) (k q v : Momentum) (side : ℝ) : ℝ :=
  (∑ r ∈ roots, rk r v * sinc (a * rk r q / 2) *
    sin (a * rk r k + side * (a * rk r q / 2))) / (6 * a)

/-- Opposite-momentum contact vertex contracted with two probe directions. -/
def contact (a : ℝ) (k q u v : Momentum) : ℝ :=
  (∑ r ∈ roots, cos (a * rk r k) * (rk r u * sinc (a * rk r q / 2)) *
    (rk r v * sinc (a * rk r q / 2))) / 6

private theorem scaled_sinc {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    a * (b * sinc (a*b/2)) = 2 * sin (a*b/2) := by
  by_cases hb : b = 0
  · simp [hb]
  · have hx : a*b/2 ≠ 0 := div_ne_zero (mul_ne_zero ha hb) (by norm_num)
    rw [Real.sinc_of_ne_zero hx]
    field_simp

theorem leg_ward {a : ℝ} (ha : a ≠ 0) (k q : Momentum) :
    leg a k q q 1 = symbol a (k+q) - symbol a k := by
  rw [ward, contracted, leg]
  apply (div_eq_div_iff (mul_ne_zero (by norm_num) ha)
    (mul_ne_zero (by norm_num) (pow_ne_zero _ ha))).2
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  simp only [one_mul]
  linear_combination (6 * a * sin (a * rk r k + a * rk r q / 2)) * scaled_sinc ha (rk r q)

theorem contact_ward {a : ℝ} (ha : a ≠ 0) (k q v : Momentum) :
    contact a k q q v = leg a k q v 1 - leg a k q v (-1) := by
  rw [contact, leg, leg, ← sub_div, ← Finset.sum_sub_distrib]
  rw [← div_div, div_right_comm]
  congr 1
  apply (eq_div_iff ha).2
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg, sin_add, sin_sub]
  linear_combination (cos (a * rk r k) * (rk r v * sinc (a * rk r q / 2))) * scaled_sinc ha (rk r q)

/-- Contracting bubble minus contact leaves the difference of two momentum routings. -/
theorem bubble_sub_contact {a : ℝ} (ha : a ≠ 0) (k q v : Momentum)
    (hk : symbol a k ≠ 0) (hkq : symbol a (k+q) ≠ 0) :
    leg a k q q 1 * leg a k q v 1 / (symbol a k * symbol a (k+q)) -
      contact a k q q v / symbol a k =
    leg a k q v (-1) / symbol a k - leg a k q v 1 / symbol a (k+q) := by
  rw [leg_ward ha, contact_ward ha]
  field_simp
  ring

end PMAction.PolarizationContact
