import PMAction.MassGap.GapFromDecay
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# From decay of truncated correlations to a spectral gap

`PolymerCorrelation.cross_ratio` bounds truncated (connected) correlations between a
modification near slice `0` and one near slice `L`. This file turns such a bound into a bound on
every eigenvalue of the transfer matrix below the top one.

For a symmetric transfer matrix `T`, a positive boundary vector `v₀` (the free end of the slab),
and an eigenvector `ψ` with eigenvalue `λ`, the slab quantities are
`Z_L = ⟨v₀, Tᴸ v₀⟩`, `⟨ψ, Tᴸ ψ⟩ = λᴸ ‖ψ‖²`, `⟨ψ, Tᴸ v₀⟩ = λᴸ ⟨ψ, v₀⟩`.
The truncated two-point function of the observable `ψ` between the two ends is
`⟨ψ, Tᴸ ψ⟩ Z_L − ⟨ψ, Tᴸ v₀⟩²`.

* `rate_of_asymptotics` (real numbers only): if `0 ≤ λ < Λ`, `κ Λᴸ ≤ Z_L ≤ K Λᴸ` and
  `λᴸ N Z_L ≤ λ^{2L} B + C ρᴸ Z_L²` for all `L` (with `N > 0`), then `λ ≤ ρ Λ`.
* `gap_of_truncated_decay`: the matrix form. If the truncated two-point function of `ψ` is at
  most `C ρᴸ Z_L²` for every `L`, then `λ ≤ ρ Λ`, so the gap per tick is at least `−log ρ`.

The hypotheses `κ Λᴸ ≤ Z_L ≤ K Λᴸ` are the statement that `Λ` is the top of the spectrum and that
`v₀` overlaps its eigenvector (true for a positive `v₀` and a positive `T`, Perron–Frobenius).
-/

namespace PMAction.MassGap.GapFromCorrelation
open Matrix Filter

/-- **Rate from asymptotics.** -/
theorem rate_of_asymptotics {lam Λ ρ N B C κ K : ℝ} (hlam0 : 0 ≤ lam) (hlamΛ : lam < Λ)
    (hρ : 0 < ρ) (hN : 0 < N) (hB : 0 ≤ B) (hC : 0 ≤ C) (hκ : 0 < κ) (hK : 0 ≤ K)
    (Zs : ℕ → ℝ) (hZlo : ∀ L, κ * Λ ^ L ≤ Zs L) (hZhi : ∀ L, Zs L ≤ K * Λ ^ L)
    (hcor : ∀ L, lam ^ L * N * Zs L ≤ lam ^ (2 * L) * B + C * ρ ^ L * Zs L ^ 2) :
    lam ≤ ρ * Λ := by
  have hΛ : 0 < Λ := lt_of_le_of_lt hlam0 hlamΛ
  by_contra hcon
  push Not at hcon
  -- `r = λ/Λ ∈ (ρ, 1)`
  set r := lam / Λ with hr
  have hr1 : r < 1 := by rw [hr, div_lt_one hΛ]; exact hlamΛ
  have hρr : ρ < r := by rw [hr, lt_div_iff₀ hΛ]; exact hcon
  have hr0 : 0 < r := lt_trans hρ hρr
  have hlam : lam = r * Λ := by rw [hr]; field_simp
  -- divide by `Z_L Λᴸ`
  have key : ∀ L, N ≤ r ^ L * (B / κ) + C * K * (ρ / r) ^ L := by
    intro L
    have hZ : 0 < Zs L := lt_of_lt_of_le (by positivity) (hZlo L)
    have hΛL : 0 < Λ ^ L := pow_pos hΛ L
    have hrL : 0 < r ^ L := pow_pos hr0 L
    have h := hcor L
    have e1 : lam ^ L = r ^ L * Λ ^ L := by rw [hlam, mul_pow]
    have e2 : lam ^ (2 * L) = (r ^ L * Λ ^ L) ^ 2 := by rw [pow_mul', e1]
    rw [e1, e2] at h
    -- `rᴸ Λᴸ N Z ≤ r^{2L} Λ^{2L} B + C ρᴸ Z²`
    have h1 : (r ^ L * Λ ^ L) ^ 2 * B ≤ (r ^ L) ^ 2 * Λ ^ L * (B / κ) * Zs L := by
      have : Λ ^ L * B ≤ (B / κ) * Zs L := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
        nlinarith [hZlo L, mul_le_mul_of_nonneg_left (hZlo L) hB]
      have hp : 0 ≤ (r ^ L) ^ 2 * Λ ^ L := by positivity
      calc (r ^ L * Λ ^ L) ^ 2 * B = (r ^ L) ^ 2 * Λ ^ L * (Λ ^ L * B) := by ring
        _ ≤ (r ^ L) ^ 2 * Λ ^ L * ((B / κ) * Zs L) := mul_le_mul_of_nonneg_left this hp
        _ = (r ^ L) ^ 2 * Λ ^ L * (B / κ) * Zs L := by ring
    have h2 : C * ρ ^ L * Zs L ^ 2 ≤ C * ρ ^ L * (K * Λ ^ L) * Zs L := by
      have hCρ : 0 ≤ C * ρ ^ L := by positivity
      rw [sq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hZhi L) hCρ) hZ.le
    have h3 : r ^ L * Λ ^ L * N * Zs L ≤
        ((r ^ L) ^ 2 * Λ ^ L * (B / κ) + C * ρ ^ L * (K * Λ ^ L)) * Zs L := by
      have := h.trans (add_le_add h1 h2)
      linarith
    have h4 : r ^ L * Λ ^ L * N ≤ (r ^ L) ^ 2 * Λ ^ L * (B / κ) + C * ρ ^ L * (K * Λ ^ L) :=
      le_of_mul_le_mul_right (by linarith) hZ
    have hρL : ρ ^ L = r ^ L * (ρ / r) ^ L := by
      rw [← mul_pow]; congr 1; field_simp
    rw [hρL] at h4
    have h5 : (r ^ L * Λ ^ L) * N ≤ (r ^ L * Λ ^ L) * (r ^ L * (B / κ) + C * K * (ρ / r) ^ L) := by
      nlinarith [h4]
    exact le_of_mul_le_mul_left h5 (mul_pos hrL hΛL)
  -- both terms go to zero
  have hq1 : ρ / r < 1 := by rw [div_lt_one hr0]; exact hρr
  have hq0 : 0 ≤ ρ / r := by positivity
  obtain ⟨L1, hL1⟩ := exists_pow_lt_of_lt_one (show 0 < N / 2 / (B / κ + 1) by positivity) hr1
  obtain ⟨L2, hL2⟩ := exists_pow_lt_of_lt_one (show 0 < N / 2 / (C * K + 1) by positivity) hq1
  set L := max L1 L2
  have e1 : r ^ L ≤ r ^ L1 := pow_le_pow_of_le_one hr0.le hr1.le (le_max_left _ _)
  have e2 : (ρ / r) ^ L ≤ (ρ / r) ^ L2 := pow_le_pow_of_le_one hq0 hq1.le (le_max_right _ _)
  have hBk : 0 ≤ B / κ := div_nonneg hB hκ.le
  have t1 : r ^ L * (B / κ) < N / 2 := by
    have : r ^ L * (B / κ) ≤ r ^ L1 * (B / κ + 1) := by
      have := pow_nonneg hr0.le L
      nlinarith
    have h' : r ^ L1 * (B / κ + 1) < N / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hL1; linarith
    linarith
  have t2 : C * K * (ρ / r) ^ L < N / 2 := by
    have hCK : 0 ≤ C * K := mul_nonneg hC hK
    have : C * K * (ρ / r) ^ L ≤ (ρ / r) ^ L2 * (C * K + 1) := by
      have := pow_nonneg hq0 L
      nlinarith
    have h' : (ρ / r) ^ L2 * (C * K + 1) < N / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hL2; linarith
    linarith
  linarith [key L]

/-- **Gap from truncated decay (matrix form).** -/
theorem gap_of_truncated_decay {n : Type*} [Fintype n] (T : Matrix n n ℝ) (hT : Matrix.IsSymm T)
    (v₀ ψ : n → ℝ) (hψ0 : ψ ≠ 0) (lam Λ : ℝ) (hψ : T *ᵥ ψ = lam • ψ) (hlam0 : 0 ≤ lam)
    (hlamΛ : lam < Λ) (κ K : ℝ) (hκ : 0 < κ) (hK : 0 ≤ K)
    (hZlo : ∀ L : ℕ, κ * Λ ^ L ≤ v₀ ⬝ᵥ (T.mulVec)^[L] v₀)
    (hZhi : ∀ L : ℕ, v₀ ⬝ᵥ (T.mulVec)^[L] v₀ ≤ K * Λ ^ L)
    (ρ C : ℝ) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (htrunc : ∀ L : ℕ, (ψ ⬝ᵥ (T.mulVec)^[L] ψ) * (v₀ ⬝ᵥ (T.mulVec)^[L] v₀) -
        (ψ ⬝ᵥ (T.mulVec)^[L] v₀) ^ 2 ≤ C * ρ ^ L * (v₀ ⬝ᵥ (T.mulVec)^[L] v₀) ^ 2) :
    lam ≤ ρ * Λ := by
  have hN : 0 < ψ ⬝ᵥ ψ := by
    have hnn : 0 ≤ ψ ⬝ᵥ ψ := Finset.sum_nonneg fun i _ => mul_self_nonneg (ψ i)
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.mp h.symm) hψ0
  -- `⟨ψ, Tᴸ v₀⟩ = λᴸ ⟨ψ, v₀⟩` by symmetry
  have hsym : ∀ L : ℕ, ψ ⬝ᵥ (T.mulVec)^[L] v₀ = lam ^ L * (ψ ⬝ᵥ v₀) := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Function.iterate_succ_apply', dotProduct_mulVec, ← mulVec_transpose, hT.eq, hψ,
        smul_dotProduct, smul_eq_mul, ih, pow_succ]
      ring
  have heig : ∀ L : ℕ, ψ ⬝ᵥ (T.mulVec)^[L] ψ = lam ^ L * (ψ ⬝ᵥ ψ) := by
    intro L
    rw [GapFromDecay.iterate_eigen T ψ lam hψ L, dotProduct_smul, smul_eq_mul]
  refine rate_of_asymptotics hlam0 hlamΛ hρ hN (sq_nonneg (ψ ⬝ᵥ v₀)) hC hκ hK
    (fun L => v₀ ⬝ᵥ (T.mulVec)^[L] v₀) hZlo hZhi ?_
  intro L
  have h := htrunc L
  rw [heig L, hsym L] at h
  have e : (lam ^ L * (ψ ⬝ᵥ v₀)) ^ 2 = lam ^ (2 * L) * (ψ ⬝ᵥ v₀) ^ 2 := by
    rw [pow_mul]; ring
  rw [e] at h
  linarith

end PMAction.MassGap.GapFromCorrelation
