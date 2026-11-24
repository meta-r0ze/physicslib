import PMConstants.CPPhases
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The vacuum weight of the winding sectors, and which CP-conserving vacuum persists

Paper II's two-tick transfer matrix is `e^{−H}`, a positive operator, so the weights `w_n` of the
winding sectors are nonnegative. The vacuum weight is `Z(θ) = Σₙ wₙ e^{inθ}` and the cost is
`−log Z`.

* `Z_zero`: `Z(0)` is the total weight.
* `theta_zero_maximal`: `‖Z(θ)‖ ≤ Z(0)` for every `θ`, so the cost is lowest at `θ = 0`.
* `Z_pi`: `Z(π)` is the alternating total.
* `theta_pi_costlier`: if any odd winding sector has positive weight, `Re Z(π) < Z(0)` strictly.

So the persistent vacuum is `θ = 0`. `VacuumModulus` strengthens this to the modulus cost,
`PersistenceClosures` reads it as a closure, `WindingWeights` and `SubstrateCharge` supply the
weights, and `ThetaBarSelection` shifts it to `θ̄`. `HermitianMass` holds the separate, superseded
Hermitian-link route to `θ̄`.
-/

noncomputable section
namespace PMConstants.VacuumWeight
open Matrix Complex ComplexConjugate

/-- Vacuum weight of the winding sectors `S` with nonnegative weights `w`. -/
def Z (S : Finset ℤ) (w : ℤ → ℝ) (θ : ℝ) : ℂ :=
  ∑ n ∈ S, (w n : ℂ) * Complex.exp (((n : ℝ) * θ : ℝ) * I)

theorem Z_zero (S : Finset ℤ) (w : ℤ → ℝ) : Z S w 0 = ((∑ n ∈ S, w n : ℝ) : ℂ) := by
  simp [Z]

theorem theta_zero_maximal (S : Finset ℤ) (w : ℤ → ℝ) (hw : ∀ n, 0 ≤ w n) (θ : ℝ) :
    ‖Z S w θ‖ ≤ ∑ n ∈ S, w n := by
  unfold Z
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hw n)]

theorem Z_pi (S : Finset ℤ) (w : ℤ → ℝ) :
    Z S w Real.pi = ((∑ n ∈ S, w n * (-1 : ℝ) ^ n.natAbs : ℝ) : ℂ) := by
  unfold Z
  push_cast
  refine Finset.sum_congr rfl (fun n _ => ?_)
  congr 1
  rw [show (n : ℂ) * (Real.pi : ℂ) * I = (n : ℂ) * (Real.pi * I) by ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg n
  · subst hk; simp
  · subst hk; rw [_root_.zpow_neg, zpow_natCast]; simp [← inv_pow]

theorem theta_pi_costlier (S : Finset ℤ) (w : ℤ → ℝ) (hw : ∀ n, 0 ≤ w n)
    {n₀ : ℤ} (hn₀ : n₀ ∈ S) (hodd : Odd n₀.natAbs) (hpos : 0 < w n₀) :
    (Z S w Real.pi).re < ∑ n ∈ S, w n := by
  rw [Z_pi, Complex.ofReal_re]
  apply Finset.sum_lt_sum
  · intro n _
    rcases neg_one_pow_eq_or ℝ n.natAbs with h | h <;> rw [h] <;> nlinarith [hw n]
  · refine ⟨n₀, hn₀, ?_⟩
    rw [hodd.neg_one_pow]; linarith

end PMConstants.VacuumWeight
