import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# From Euclidean decay to a spectral gap

The cluster expansion delivers decay of Euclidean (imaginary-time) correlations: for an observable
`v` orthogonal to the vacuum, `⟨v, Tᵗ v⟩ ≤ C λᵗ` for every number of ticks `t`. This file proves
the step from that decay to a spectral statement about the one-tick transfer matrix `T`.

* `iterate_eigen`: if `T v = μ v` then `t` ticks give `μᵗ v`.
* `eigen_le_of_decay`: if `v ≠ 0` is an eigenvector with eigenvalue `μ` and
  `⟨v, Tᵗ v⟩ ≤ C λᵗ` for all `t` (with `λ > 0`), then `|μ| ≤ λ`. Neither symmetry nor any bound on
  `C` is needed. Decay holding at all times caps the eigenvalue.
* `gap_of_decay`: if every eigenvector in the excited sector decays at the same rate `λ < 1`, then
  every excited eigenvalue satisfies `|μ| ≤ λ`. With the vacuum eigenvalue normalized to `1`, the
  mass gap per tick is at least `−log λ > 0`.

Combined with `PolymerConvergence` and `ContourCount`, the remaining analytic input for a
volume-uniform gap is a volume-uniform `λ`, which is the decay-of-correlations estimate.
-/

namespace PMAction.MassGap.GapFromDecay
open Matrix

variable {n : Type*} [Fintype n]

/-- `t` ticks on an eigenvector multiply it by `μᵗ`. -/
theorem iterate_eigen (T : Matrix n n ℝ) (v : n → ℝ) (μ : ℝ) (hv : T *ᵥ v = μ • v) (t : ℕ) :
    (T.mulVec)^[t] v = μ ^ t • v := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, mulVec_smul, hv, smul_smul, pow_succ, mul_comm]

/-- `r^s` with `r > 1` eventually exceeds any bound. -/
lemma not_bounded_pow {r B : ℝ} (hr : 1 < r) : ¬ ∀ s : ℕ, r ^ s ≤ B := by
  intro h
  obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt B hr
  linarith [h s]

/-- **Decay at all times caps the eigenvalue.** -/
theorem eigen_le_of_decay (T : Matrix n n ℝ) (v : n → ℝ) (hv0 : v ≠ 0) (μ : ℝ)
    (hv : T *ᵥ v = μ • v) (C lam : ℝ) (hlam : 0 < lam)
    (hdec : ∀ t : ℕ, v ⬝ᵥ (T.mulVec)^[t] v ≤ C * lam ^ t) : |μ| ≤ lam := by
  have hvv : 0 < v ⬝ᵥ v := by
    have hnn : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.mp h.symm) hv0
  by_contra hcon
  push Not at hcon
  set r : ℝ := (μ / lam) ^ 2 with hr
  have hμ2 : lam ^ 2 < μ ^ 2 := by
    have h0 : 0 ≤ lam := hlam.le
    nlinarith [abs_nonneg μ, sq_abs μ]
  have hr1 : 1 < r := by
    rw [hr, div_pow, one_lt_div (by positivity)]
    exact hμ2
  apply not_bounded_pow hr1 (B := C / (v ⬝ᵥ v))
  intro s
  have h := hdec (2 * s)
  rw [iterate_eigen T v μ hv, dotProduct_smul, smul_eq_mul] at h
  have hl : 0 < lam ^ (2 * s) := by positivity
  rw [le_div_iff₀ hvv, hr, ← pow_mul, div_pow]
  rw [div_mul_eq_mul_div, div_le_iff₀ hl]
  calc μ ^ (2 * s) * (v ⬝ᵥ v) = v ⬝ᵥ v * μ ^ (2 * s) := by ring
    _ ≤ C * lam ^ (2 * s) := by rw [mul_comm (v ⬝ᵥ v)]; linarith [h]

/-- **Gap from uniform decay.** If every eigenvector in the excited sector (`excited v`) decays at
rate `λ` with some constant, every excited eigenvalue is at most `λ` in absolute value. -/
theorem gap_of_decay (T : Matrix n n ℝ) (excited : (n → ℝ) → Prop) (lam : ℝ) (hlam : 0 < lam)
    (hdec : ∀ v, excited v → ∃ C, ∀ t : ℕ, v ⬝ᵥ (T.mulVec)^[t] v ≤ C * lam ^ t)
    (v : n → ℝ) (hv0 : v ≠ 0) (hex : excited v) (μ : ℝ) (hv : T *ᵥ v = μ • v) : |μ| ≤ lam := by
  obtain ⟨C, hC⟩ := hdec v hex
  exact eigen_le_of_decay T v hv0 μ hv C lam hlam hC

end PMAction.MassGap.GapFromDecay
