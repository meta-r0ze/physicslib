import PMAction.OtherWallStationary
import PMAction.ExactZeroMode
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Lifting the wire's resonant zero

The bare wire is singular at the stationary cycle resonance. Multiplying
it by dressing matrices leaves it singular. An additive shift on one
diagonal leg instead changes the determinant by exactly `δ² ε` in the
other-wall factor, with no fitted input. The effect on the full zero-energy
kernel is exact in the two-wall Hamiltonian.

A freely selectable common detuning can restore a zero even after a fixed
additive perturbation. Thus a physical lifting mechanism must also explain
which detuning is held fixed or shared.
-/

noncomputable section
namespace PMElementaryParticles.ResonanceLift

open Matrix PMAction
open ReferenceWallRotation CyclicSeesaw

/-- Generation-dependent on-site detunings with the existing cyclic support. -/
def wall (d κ : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagonal d + cyc κ

theorem det_wall (d κ : Fin 3 → ℂ) :
    (wall d κ).det = d 0 * d 1 * d 2 + κ 0 * κ 1 * κ 2 := by
  rw [wall, det_fin_three]
  simp [cyc]
  ring

/-- Add an offset on one generation's diagonal flip leg. -/
def shifted (δ : ℂ) (κ : Fin 3 → ℂ) (j : Fin 3) (ε : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  wall (fun i => δ + if i = j then ε else 0) κ

@[simp]
theorem shifted_zero (δ : ℂ) (κ : Fin 3 → ℂ) (j : Fin 3) :
    shifted δ κ j 0 = X δ κ := by
  simp [shifted, wall, X, smul_one_eq_diagonal]

theorem det_shifted (δ : ℂ) (κ : Fin 3 → ℂ) (j : Fin 3) (ε : ℂ) :
    (shifted δ κ j ε).det = δ ^ 3 + κ 0 * κ 1 * κ 2 + δ ^ 2 * ε := by
  rw [shifted, det_wall]
  fin_cases j <;> norm_num <;> ring

theorem det_shifted_at_resonance (δ : ℂ) (κ : Fin 3 → ℂ) (j : Fin 3) (ε : ℂ)
    (hδ : δ ^ 3 = -(κ 0 * κ 1 * κ 2)) :
    (shifted δ κ j ε).det = δ ^ 2 * ε := by
  rw [det_shifted, hδ, neg_add_cancel, zero_add]

/-- The one-leg insertion with the same determinant as shifting all
three legs by `t`. The cycle product cancels in the comparison. -/
def determinantMatchedOffset (δ t : ℂ) : ℂ :=
  ((δ + t) ^ 3 - δ ^ 3) / δ ^ 2

theorem det_shifted_eq_uniform_iff (δ t ε : ℂ) (κ : Fin 3 → ℂ) (j : Fin 3)
    (hδ : δ ≠ 0) :
    (shifted δ κ j ε).det = (X (δ + t) κ).det ↔
      ε = determinantMatchedOffset δ t := by
  rw [det_shifted, det_X, determinantMatchedOffset, eq_div_iff (pow_ne_zero 2 hδ)]
  constructor <;> intro h <;> linear_combination h

/-- At the normalized real detuning, the determinant-matched insertion
is cubic in the uniform offset. -/
theorem determinantMatchedOffset_neg_one (t : ℂ) :
    determinantMatchedOffset (-1) t = 3 * t - 3 * t ^ 2 + t ^ 3 := by
  unfold determinantMatchedOffset
  ring

/-- Matching the determinant leaves a difference in the sum of squared
singular values of the unweighted wall. With uniform detuning `-z`, the
determinant-matched single leg has detuning `-z³` and the other two stay
at `-1`. The trace gap vanishes only for `z² = 1`. -/
theorem det_matched_trace_gap (κ : Fin 3 → ℂ) (j : Fin 3) (z : ℝ) :
    let A := shifted (-1) κ j (1 - (z : ℂ) ^ 3)
    let U := X (-(z : ℂ)) κ
    (A * Aᴴ).trace.re - (U * Uᴴ).trace.re = (z ^ 2 - 1) ^ 2 * (z ^ 2 + 2) := by
  fin_cases j <;>
    simp [shifted, wall, X, trace, diag, Matrix.mul_apply, Matrix.add_apply,
      conjTranspose_apply, cyc, Fin.sum_univ_three, diagonal, one_apply, vecHead,
      vecTail, Complex.add_re, Complex.mul_re, pow_succ] <;> ring

/-- Multiplicative dressing preserves the zero determinant at resonance. -/
theorem dressed_det_zero (A B : Matrix (Fin 3) (Fin 3) ℂ) (δ : ℂ) (κ : Fin 3 → ℂ)
    (hδ : δ ^ 3 = -(κ 0 * κ 1 * κ 2)) :
    (A * X δ κ * B).det = 0 := by
  simp [det_mul, det_X, hδ]

/-- With nonzero detuning, different single-leg offsets cannot both be
resonant at the same common detuning and cycle product. -/
theorem unique_offset_at_shared_detuning (δ : ℂ) (κ : Fin 3 → ℂ)
    (j k : Fin 3) (ε η : ℂ) (hδ : δ ≠ 0)
    (hε : (shifted δ κ j ε).det = 0) (hη : (shifted δ κ k η).det = 0) : ε = η := by
  rw [det_shifted] at hε hη
  apply mul_left_cancel₀ (pow_ne_zero 2 hδ)
  exact add_left_cancel (hε.trans hη.symm)

/-- A free complex detuning can tune the fixed perturbed wall to a zero
of the same secular determinant. -/
theorem retuning_exists (A : Matrix (Fin 3) (Fin 3) ℂ) :
    ∃ δ : ℂ, (δ • (1 : Matrix (Fin 3) (Fin 3) ℂ) + A).det = 0 := by
  have hdeg : (-A).charpoly.degree ≠ 0 := by simp
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_root (-A).charpoly hdeg
  refine ⟨δ, ?_⟩
  rw [Polynomial.IsRoot, eval_charpoly, sub_neg_eq_add] at hδ
  rw [smul_one_eq_diagonal]
  exact hδ

private theorem negative_cubic_root (cycle ε : ℝ) (hc : 0 < cycle) :
    ∃ δ : ℝ, δ < 0 ∧ δ ^ 2 * (δ + ε) + cycle = 0 := by
  let lo := -(|ε| + cycle + 1)
  let f := fun x : ℝ => x ^ 2 * (x + ε) + cycle
  have hlo : lo ≤ -1 := by dsimp [lo]; linarith [abs_nonneg ε]
  have hshift : lo + ε ≤ -(cycle + 1) := by dsimp [lo]; linarith [le_abs_self ε]
  have hsq : 1 ≤ lo ^ 2 := by nlinarith [sq_nonneg (lo + 1)]
  have hfl : f lo ≤ 0 := calc
    f lo ≤ lo ^ 2 * (-(cycle + 1)) + cycle :=
      by simpa [f, add_comm] using
        (add_le_add_right (mul_le_mul_of_nonneg_left hshift (sq_nonneg lo)) cycle)
    _ ≤ 0 := by nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (show 0 ≤ cycle + 1 by linarith)]
  have hf₀ : f 0 = cycle := by simp [f]
  have hf : Continuous f := by unfold f; fun_prop
  obtain ⟨δ, hδ, hz⟩ :=
    intermediate_value_Icc (show lo ≤ 0 by linarith) hf.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (f lo) (f 0) from ⟨hfl, hf₀ ▸ hc.le⟩)
  refine ⟨δ, lt_of_le_of_ne hδ.2 ?_, hz⟩
  intro h
  rw [h, hf₀] at hz
  exact hc.ne' hz

/-- A positive cycle product can retune even if the common detuning must
stay on the negative real branch. -/
theorem negative_retuning_exists (κ : Fin 3 → ℂ) (j : Fin 3) (cycle ε : ℝ)
    (hc : 0 < cycle) (hκ : κ 0 * κ 1 * κ 2 = (cycle : ℂ)) :
    ∃ δ : ℝ, δ < 0 ∧ (shifted δ κ j ε).det = 0 := by
  obtain ⟨δ, hδ, hz⟩ := negative_cubic_root cycle ε hc
  refine ⟨δ, hδ, ?_⟩
  calc
    (shifted δ κ j ε).det = ((δ ^ 2 * (δ + ε) + cycle : ℝ) : ℂ) := by
      rw [det_shifted, hκ]
      push_cast
      ring
    _ = 0 := by simp [hz]

section Full
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If the crossing and the reference flip are invertible, the other-wall
factor is singular exactly when the full Hamiltonian has a zero mode. -/
theorem full_zero_iff (Y R A : Matrix n n ℂ) (hY : IsUnit Y.det) (hR : IsUnit R.det) :
    (∃ w, w ≠ 0 ∧ ExactZeroMode.H Y Aᴴ R *ᵥ w = 0) ↔ A.det = 0 := by
  constructor
  · rintro ⟨w, hw, hz⟩
    by_contra hA
    let V := CompositeMass.V2 Aᴴ R
    have hV : IsUnit V.det := by
      change IsUnit (CompositeMass.V2 Aᴴ R).det
      rw [CompositeMass.V2, det_fromBlocks_zero₂₁, det_conjTranspose]
      exact (isUnit_iff_ne_zero.mpr hA).star.mul hR
    have hVh : IsUnit Vᴴ.det := by rw [det_conjTranspose]; exact hV.star
    let x := w ∘ Sum.inl
    let z := w ∘ Sum.inr
    rw [ExactZeroMode.H, fromBlocks_mulVec] at hz
    have hz₀ : z = 0 := by
      by_contra h
      apply hV.ne_zero
      apply exists_mulVec_eq_zero_iff.mp
      refine ⟨z, h, ?_⟩
      funext i
      simpa [V, z] using congrFun hz (Sum.inl i)
    have hx₀ : x = 0 := by
      by_contra h
      apply hVh.ne_zero
      apply exists_mulVec_eq_zero_iff.mp
      refine ⟨x, h, ?_⟩
      funext i
      have hi := congrFun hz (Sum.inr i)
      change (Vᴴ *ᵥ x + WallSeesaw.G Y *ᵥ z) i = 0 at hi
      simpa [hz₀] using hi
    apply hw
    funext i
    cases i with
    | inl i => exact congrFun hx₀ i
    | inr i => exact congrFun hz₀ i
  · intro hA
    obtain ⟨v, hv, hAv⟩ := exists_mulVec_eq_zero_iff.mpr hA
    apply ExactZeroMode.exact_zero_mode Y Aᴴ R hY v hv
    rw [conjTranspose_conjTranspose, ← mulVec_mulVec, hAv, mulVec_zero]

end Full

/-- The exact determinant of the charged Schur mass from a single added leg
at the bare resonance. -/
theorem shifted_schur_det (Y R : Matrix (Fin 3) (Fin 3) ℂ) (δ : ℂ) (κ : Fin 3 → ℂ)
    (j : Fin 3) (ε : ℂ) (hδ : δ ^ 3 = -(κ 0 * κ 1 * κ 2)) :
    (R * Y⁻¹ * shifted δ κ j ε).det = R.det * (Y.det)⁻¹ * (δ ^ 2 * ε) := by
  rw [det_mul, det_mul, det_nonsing_inv, Ring.inverse_eq_inv',
    det_shifted_at_resonance δ κ j ε hδ]

/-- A nonzero single-leg offset at fixed nonzero resonance removes the full
Hamiltonian zero mode, for any invertible crossing and reference flip. -/
theorem shifted_full_zero_iff (Y R : Matrix (Fin 3) (Fin 3) ℂ)
    (hY : IsUnit Y.det) (hR : IsUnit R.det) (δ : ℂ) (κ : Fin 3 → ℂ)
    (hδ₀ : δ ≠ 0) (hδ : δ ^ 3 = -(κ 0 * κ 1 * κ 2)) (j : Fin 3) (ε : ℂ) :
    (∃ w, w ≠ 0 ∧ ExactZeroMode.H Y (shifted δ κ j ε)ᴴ R *ᵥ w = 0) ↔ ε = 0 := by
  rw [full_zero_iff Y R _ hY hR, det_shifted_at_resonance δ κ j ε hδ]
  rw [mul_eq_zero, or_iff_right (pow_ne_zero 2 hδ₀)]

end PMElementaryParticles.ResonanceLift
