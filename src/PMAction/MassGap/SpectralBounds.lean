import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Spectral bounds for the free-end partition function

For a real symmetric matrix `T` and a vector `v`:

* `spectral_sum`: `v ⬝ Tᴸ v = Σ_j c_j λ_jᴸ` with weights `c_j = (v ⬝ e_j)² ≥ 0` summing to
  `v ⬝ v` (orthonormal eigenbasis, Mathlib's spectral theorem).
* `iterate_sq`: `(T²)ᴸ = T^{2L}` on vectors.
* `visible_top`: for `S = T²` and `v ≠ 0` there are `Λ ≥ 0`, `κ > 0`, `K ≥ 0` with
  `κ Λᴸ ≤ v ⬝ Sᴸ v ≤ K Λᴸ` for all `L`. `Λ` is the largest eigenvalue of `S` that `v` sees.
* `rate_le`: if `aᴸ N ≤ C bᴸ` for all `L`, with `N > 0` and `a, b ≥ 0`, then `a ≤ b`.
* `dot_iterate_comm`: `x ⬝ Sᴸ y = y ⬝ Sᴸ x` for symmetric `S`.
-/

namespace PMAction.MassGap.SpectralBounds
open Finset Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma iterate_eig (A : Matrix n n ℝ) (e : n → ℝ) (lam : ℝ) (h : A *ᵥ e = lam • e) :
    ∀ L : ℕ, (A.mulVec)^[L] e = lam ^ L • e := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Function.iterate_succ_apply', ih, mulVec_smul, h, smul_smul, pow_succ]

omit [DecidableEq n] in
lemma iterate_sum (A : Matrix n n ℝ) (e : n → n → ℝ) (lam w : n → ℝ)
    (h : ∀ j, A *ᵥ e j = lam j • e j) :
    ∀ L : ℕ, (A.mulVec)^[L] (∑ j, w j • e j) = ∑ j, (w j * lam j ^ L) • e j := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Function.iterate_succ_apply', ih, mulVec_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [mulVec_smul, h, smul_smul, pow_succ]; ring_nf

/-- **Spectral sum.** -/
theorem spectral_sum (T : Matrix n n ℝ) (hT : T.IsHermitian) (v : n → ℝ) :
    ∃ c lam : n → ℝ, (∀ j, 0 ≤ c j) ∧
      ∀ L : ℕ, v ⬝ᵥ (T.mulVec)^[L] v = ∑ j, c j * lam j ^ L := by
  set e : n → n → ℝ := fun j => ⇑(hT.eigenvectorBasis j)
  set U : Matrix n n ℝ := (hT.eigenvectorUnitary : Matrix n n ℝ)
  set w : n → ℝ := fun j => v ⬝ᵥ e j
  have hUe : ∀ i j, U i j = e j i := fun i j => rfl
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hv : v = ∑ j, w j • e j := by
    have h1 : U *ᵥ (star U *ᵥ v) = v := by rw [mulVec_mulVec, hUU, one_mulVec]
    conv_lhs => rw [← h1]
    funext i
    simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, w, hUe,
      star_apply, star_trivial]
    refine sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine sum_congr rfl fun k _ => ?_
    ring
  have heig : ∀ j, T *ᵥ e j = hT.eigenvalues j • e j := fun j => hT.mulVec_eigenvectorBasis j
  refine ⟨fun j => w j ^ 2, hT.eigenvalues, fun j => sq_nonneg _, fun L => ?_⟩
  have hit := iterate_sum T e hT.eigenvalues w heig L
  rw [← hv] at hit
  rw [hit, dotProduct_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [dotProduct_smul, smul_eq_mul]
  show w j * hT.eigenvalues j ^ L * w j = _
  ring

omit [DecidableEq n] in
lemma iterate_sq (T : Matrix n n ℝ) (v : n → ℝ) :
    ∀ L : ℕ, ((T * T).mulVec)^[L] v = (T.mulVec)^[2 * L] v := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Function.iterate_succ_apply', ih, show 2 * (L + 1) = 2 * L + 1 + 1 by ring,
      Function.iterate_succ_apply', Function.iterate_succ_apply', mulVec_mulVec]

/-- **The visible top.** -/
theorem visible_top (T : Matrix n n ℝ) (hT : T.IsHermitian) (v : n → ℝ) (hv : v ≠ 0) :
    ∃ Λ κ K : ℝ, 0 ≤ Λ ∧ 0 < κ ∧ 0 ≤ K ∧ ∀ L : ℕ,
      κ * Λ ^ L ≤ v ⬝ᵥ ((T * T).mulVec)^[L] v ∧ v ⬝ᵥ ((T * T).mulVec)^[L] v ≤ K * Λ ^ L := by
  obtain ⟨c, lam, hc, hZ⟩ := spectral_sum T hT v
  have hZS : ∀ L : ℕ, v ⬝ᵥ ((T * T).mulVec)^[L] v = ∑ j, c j * (lam j ^ 2) ^ L := by
    intro L; rw [iterate_sq, hZ]
    exact sum_congr rfl fun j _ => by rw [← pow_mul]
  have hpos : 0 < v ⬝ᵥ v := by
    have hnn : 0 ≤ v ⬝ᵥ v := sum_nonneg fun i _ => mul_self_nonneg (v i)
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exfalso; apply hv; funext i
      have := (sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (v i)).mp h.symm i (mem_univ _)
      simpa using this
  set Sset := univ.filter fun j => c j ≠ 0
  have hne : Sset.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have h0 := hZ 0
    simp only [Function.iterate_zero, id_eq, pow_zero, mul_one] at h0
    have : ∑ j, c j = 0 := sum_eq_zero fun j _ => by
      by_contra hcj
      have : j ∈ Sset := by simp [Sset, hcj]
      rw [h] at this; simp at this
    linarith
  obtain ⟨j₀, hj₀, hj₀Λ⟩ := Sset.exists_mem_eq_sup' hne fun j => lam j ^ 2
  set Λ := Sset.sup' hne fun j => lam j ^ 2
  have hΛ0 : 0 ≤ Λ := by rw [hj₀Λ]; exact sq_nonneg _
  have hle : ∀ j ∈ Sset, lam j ^ 2 ≤ Λ := fun j hj => le_sup' (fun j => lam j ^ 2) hj
  set top := Sset.filter fun j => lam j ^ 2 = Λ
  refine ⟨Λ, ∑ j ∈ top, c j, ∑ j, c j, hΛ0, ?_, sum_nonneg fun j _ => hc j, fun L => ⟨?_, ?_⟩⟩
  · have hj₀top : j₀ ∈ top := by simp [top, hj₀, ← hj₀Λ]
    have hcj₀ : 0 < c j₀ := lt_of_le_of_ne (hc j₀) (Ne.symm (mem_filter.mp hj₀).2)
    exact lt_of_lt_of_le hcj₀ (single_le_sum (fun j _ => hc j) hj₀top)
  · rw [hZS, sum_mul]
    calc ∑ j ∈ top, c j * Λ ^ L = ∑ j ∈ top, c j * (lam j ^ 2) ^ L := by
          refine sum_congr rfl fun j hj => ?_
          rw [(mem_filter.mp hj).2]
      _ ≤ ∑ j, c j * (lam j ^ 2) ^ L :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ =>
            mul_nonneg (hc j) (pow_nonneg (sq_nonneg _) _)
  · rw [hZS, sum_mul]
    refine sum_le_sum fun j _ => ?_
    by_cases hj : c j = 0
    · simp [hj]
    · have hjS : j ∈ Sset := by simp [Sset, hj]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) (hle j hjS) _) (hc j)

/-- **Rate comparison.** -/
theorem rate_le {a b N C : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 < N)
    (h : ∀ L : ℕ, a ^ L * N ≤ C * b ^ L) : a ≤ b := by
  by_contra hab
  push Not at hab
  rcases hb.lt_or_eq with hb0 | hb0
  · -- `(a/b)^L` grows without bound
    set r := a / b with hr
    have hr1 : 1 < r := by rw [hr, one_lt_div hb0]; exact hab
    have hC : ∀ L : ℕ, r ^ L * N ≤ C := by
      intro L
      have hbL : 0 < b ^ L := pow_pos hb0 L
      have := h L
      rw [hr, div_pow, div_mul_eq_mul_div, div_le_iff₀ hbL]
      linarith
    obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (C / N + 1) hr1
    have := hC L
    have h2 : C / N < r ^ L := by linarith
    rw [div_lt_iff₀ hN] at h2
    linarith
  · subst hb0
    have := h 1
    simp only [pow_one, mul_zero] at this
    have : 0 < a * N := mul_pos hab hN
    linarith

omit [DecidableEq n] in
lemma dot_mulVec_comm (S : Matrix n n ℝ) (hS : S.IsSymm) (x y : n → ℝ) :
    x ⬝ᵥ (S *ᵥ y) = y ⬝ᵥ (S *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS.eq, dotProduct_comm]

omit [DecidableEq n] in
/-- Symmetric iterates are self-adjoint. -/
lemma dot_iterate_comm (S : Matrix n n ℝ) (hS : S.IsSymm) (x y : n → ℝ) :
    ∀ L : ℕ, x ⬝ᵥ (S.mulVec)^[L] y = y ⬝ᵥ (S.mulVec)^[L] x := by
  intro L
  induction L generalizing x y with
  | zero => simp [dotProduct_comm]
  | succ L ih =>
    rw [Function.iterate_succ_apply', dot_mulVec_comm S hS, dotProduct_comm, ih,
      ← Function.iterate_succ_apply]

end PMAction.MassGap.SpectralBounds
