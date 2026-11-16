import PMAction.LocalUnitary

/-!
# Exact local unitarity forces the Wilson point on every wall

The split update's neighbour factor uses the coefficient `c = (1/2) β + (i/2) αⱼ`
(`LocalUnitary.coefficient`), and its exact unitarity rests on `c² = 0` and `c c† + c† c = 1`
(`LocalUnitary.coefficient_relations`). With a general in-wall Wilson parameter the coefficient is
`c_r = (r/2) β + (i/2) αⱼ`.

* `coeff_sq`: from `β² = α² = 1` and `βα = −αβ` alone, `c_r² = ((r² − 1)/4) · 1`.
* `nilpotent_iff`: so `c_r² = 0` exactly when `r² = 1`.

So a wall updated by the library's exactly local unitary split has `|r| = 1`: the Wilson point is
forced, not chosen. **Consequence for flavour** (PMElementaryParticles REVIEW, idea 6): a
wall-dependent Wilson parameter `r_O ≠ 1` cannot give the two walls different carrier sizes
(`CarrierFlip`: a carrier flips by `−r t/2`), unless the other wall is updated by a different,
non-split construction. That route to the `s/c` magnitude asymmetry is closed under the library's
update; recorded as a negative result.
-/

namespace PMAction.WilsonPointForced
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **`(aβ + bα)² = (a² + b²)`** for anticommuting involutions. -/
theorem sum_sq (β α : Matrix n n ℂ) (hβ : β * β = 1) (hα : α * α = 1) (hac : β * α = -(α * β))
    (a b : ℂ) : (a • β + b • α) * (a • β + b • α) = (a ^ 2 + b ^ 2) • (1 : Matrix n n ℂ) := by
  rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
    smul_mul_smul_comm, hβ, hα, hac, smul_neg]
  module

/-- **The Wilson-`r` neighbour coefficient squares to `(r² − 1)/4`.** -/
theorem coeff_sq (β α : Matrix n n ℂ) (hβ : β * β = 1) (hα : α * α = 1) (hac : β * α = -(α * β))
    (r : ℂ) :
    ((r / 2) • β + (Complex.I / 2) • α) * ((r / 2) • β + (Complex.I / 2) • α) =
      ((r ^ 2 - 1) / 4) • (1 : Matrix n n ℂ) := by
  rw [sum_sq β α hβ hα hac]
  congr 1
  rw [div_pow, div_pow, Complex.I_sq]
  ring

/-- **Nilpotent exactly at the Wilson point** (`r² = 1`), on a nonempty index set. -/
theorem nilpotent_iff [Nonempty n] (β α : Matrix n n ℂ) (hβ : β * β = 1) (hα : α * α = 1)
    (hac : β * α = -(α * β)) (r : ℂ) :
    ((r / 2) • β + (Complex.I / 2) • α) * ((r / 2) • β + (Complex.I / 2) • α) = 0 ↔ r ^ 2 = 1 := by
  rw [coeff_sq β α hβ hα hac]
  constructor
  · intro h
    obtain ⟨i⟩ := ‹Nonempty n›
    have := congrFun (congrFun h i) i
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at this
    linear_combination 4 * this
  · intro h
    rw [h]; simp
end PMAction.WilsonPointForced
