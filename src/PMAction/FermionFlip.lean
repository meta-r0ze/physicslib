import PMAction.CarrierStatistics
import Mathlib.LinearAlgebra.Determinant

/-!
# The many-flavour flip amplitude is the determinant

Part of the substrate version of the chiral-anomaly relation (`PMConstants.ThetaBarSelection`'s
premise): a unit winding flips one zero mode per flavour, and the amplitude that does it carries
`det M`.

Carriers are fermions (`CarrierStatistics.exchange_is_minus_one`): an amplitude for `n` carriers
in `n` modes is alternating in them. Flipping every flavour's zero mode through the mass bilinear
`M` (the only term joining the two walls) applies `M` to each carrier.

* `flip_amplitude`: for any alternating `n`-carrier amplitude `ψ`, applying `M` to every carrier
  multiplies it by `det M`. The determinant is the antisymmetry of the carriers, not a choice.
* `winding_phase`: `n` such flips carry `(det M)ⁿ = |det M|ⁿ e^{i n α}`, `α = arg det M`; with real
  positive masses the factor is positive.
-/

noncomputable section
namespace PMAction.FermionFlip
open Matrix

/-- **Applying `M` to every carrier multiplies an alternating amplitude by `det M`.** -/
theorem flip_amplitude {n : ℕ} (ψ : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → Fin n → ℂ) :
    ψ (fun i => M *ᵥ v i) = M.det * ψ v := by
  have h := AlternatingMap.eq_smul_basis_det (e := Pi.basisFun ℂ (Fin n)) ψ
  rw [h, AlternatingMap.smul_apply, AlternatingMap.smul_apply, smul_eq_mul, smul_eq_mul]
  have hc : (fun i => M *ᵥ v i) = Matrix.toLin' M ∘ v := by
    funext i; simp [Matrix.toLin'_apply]
  rw [hc, Module.Basis.det_comp, LinearMap.det_toLin']
  ring

/-- **`n` flips carry `|det M|ⁿ e^{i n arg det M}`.** -/
theorem winding_phase {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (n : ℕ) :
    M.det ^ n = ((‖M.det‖ ^ n : ℝ) : ℂ) *
      Complex.exp (((n : ℝ) * Complex.arg M.det : ℝ) * Complex.I) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I M.det]
  rw [mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

end PMAction.FermionFlip
