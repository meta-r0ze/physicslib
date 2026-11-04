import PMConstants.CPPhases
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Hermitian link masses: θ̄ = θ, with CP violation still allowed in mixing

`CPPhases` showed that a real update forces `θ ∈ πℤ` but would also force `J = 0`, so the
complex phases must sit in flavour mixing while the strong-CP combination
`θ̄ = θ − arg det(M_u M_d)` stays real. Paper IV's `CKM.ckm_det` shows complex mixing with a
real determinant is possible. This module supplies the mass-matrix side.

Premise (sector exchange). The two D₄ sectors are copies of the same lattice (Paper I's
`d4d4`); nothing in the substrate distinguishes them, only the vacuum's choice of which side of
the domain wall holds the left-handed states. An update coefficient that persists must then be
invariant under exchanging the sectors. Exchange maps the inter-sector link matrix `M`
(sector 1 → sector 2) to `M†` (sector 2 → sector 1), so `M = M†`.

* `det_real_of_hermitian`: a Hermitian mass matrix has real determinant.
* `arg_det_zero`: if its eigenvalues (the physical masses, positive by Paper II's
  `DetuningMass`) are positive, `arg det M = 0`.
* `thetaBar_eq_theta`: with Hermitian, positive `M_u` and `M_d`, `θ̄ = θ`. Combined with
  `CPPhases.real_weights_iff`, `θ̄ ∈ πℤ`.
* `cp_with_hermitian`: Hermitian mass matrices still violate CP. For explicit Hermitian
  `H_u = diag(1,2,3)` and complex Hermitian `H_d`, `det[H_u, H_d] = 4i ≠ 0`; Jarlskog's criterion
  `det[H_u, H_d] ∝ iJ` makes `J ≠ 0` possible.

Which of `θ = 0` and `θ = π` persists. Paper II's two-tick transfer matrix is `e^{−H}`, a
positive operator, so the weights `w_n` of the winding sectors are nonnegative. The vacuum
weight is `Z(θ) = Σₙ wₙ e^{inθ}`:

* `theta_zero_maximal`: `‖Z(θ)‖ ≤ Z(0)` for every `θ`; the cost `−log Z` is lowest at `θ = 0`.
* `theta_pi_costlier`: if any odd winding sector has positive weight, `Re Z(π) < Z(0)` strictly.

So the persistent vacuum is `θ = 0`, and with Hermitian positive link masses `θ̄ = 0`.
Remaining premise: sector-exchange invariance of the link coefficients.
-/

noncomputable section
namespace PMConstants.HermitianMass
open Matrix Complex ComplexConjugate

theorem det_real_of_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (h : Mᴴ = M) : (M.det).im = 0 := by
  have h1 := Matrix.det_conjTranspose M
  rw [h] at h1
  exact (Complex.conj_eq_iff_im.mp h1.symm)

theorem det_pos_of_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (hpos : ∀ i, 0 < hM.eigenvalues i) :
    M.det = ((∏ i, hM.eigenvalues i : ℝ) : ℂ) ∧ 0 < ∏ i, hM.eigenvalues i := by
  refine ⟨?_, Finset.prod_pos (fun i _ => hpos i)⟩
  rw [hM.det_eq_prod_eigenvalues]
  push_cast
  rfl

theorem arg_det_zero {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (hpos : ∀ i, 0 < hM.eigenvalues i) :
    (M.det).arg = 0 := by
  obtain ⟨h1, h2⟩ := det_pos_of_hermitian hM hpos
  rw [h1, Complex.arg_ofReal_of_nonneg h2.le]

/-- The strong-CP combination. -/
def thetaBar (θ : ℝ) (Mu Md : Matrix (Fin 3) (Fin 3) ℂ) : ℝ := θ - (Mu.det * Md.det).arg

theorem thetaBar_eq_theta (θ : ℝ) {Mu Md : Matrix (Fin 3) (Fin 3) ℂ}
    (hu : Mu.IsHermitian) (hd : Md.IsHermitian)
    (pu : ∀ i, 0 < hu.eigenvalues i) (pd : ∀ i, 0 < hd.eigenvalues i) :
    thetaBar θ Mu Md = θ := by
  obtain ⟨u1, u2⟩ := det_pos_of_hermitian hu pu
  obtain ⟨d1, d2⟩ := det_pos_of_hermitian hd pd
  unfold thetaBar
  rw [u1, d1, ← Complex.ofReal_mul, Complex.arg_ofReal_of_nonneg (mul_pos u2 d2).le, sub_zero]

def Hu : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 2, 0; 0, 0, 3]
def Hd : Matrix (Fin 3) (Fin 3) ℂ := !![2, I, 1; -I, 2, 1; 1, 1, 3]

theorem Hu_hermitian : Huᴴ = Hu := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Hu, Matrix.conjTranspose_apply]

theorem Hd_hermitian : Hdᴴ = Hd := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Hd, Matrix.conjTranspose_apply]

theorem cp_with_hermitian : (Hu * Hd - Hd * Hu).det = 4 * I := by
  rw [Matrix.det_fin_three]
  simp [Hu, Hd]
  ring_nf

/-! ## Which CP-conserving vacuum persists -/

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

end PMConstants.HermitianMass
