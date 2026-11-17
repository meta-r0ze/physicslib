import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# How far a light state leaks into the gapped modes

`ChiralLightBand` identifies the charged current's wall on the light band, where light states lie in
the zero kernel and wall mixing enters only through the gapped modes. It gives the projector identity,
not a bound on how much a light eigenstate leaks out of the kernel. This module gives the bound.

Split a state into its light part `x` (the zero kernel: `a`, `d` of `WallSeesaw`) and its gapped part
`z` (`b`, `c`). The eigenvalue equation's gapped row is `(G − E) z = w` with `w = −Vᴴ x`, `V` the flips
joining the two (`D₁` on wall `1`, `D₂` on wall `2`) and `G` the gapped block.

* `norm_map_of_sq`: if `G` is symmetric and `G² = g² · 1`, then `‖G z‖ = |g| ‖z‖`. For the two-wall
  block `G = [[0, −Y], [−Yᴴ, 0]]` with `Y = y · U`, `U` unitary (the premise behind `|y|`), `G² = |y|²`.
* `coercive`: so `‖(G − E) z‖ ≥ (|g| − |E|) ‖z‖`.
* `leakage_bound`: for `|E| < |g|` and `‖w‖ ≤ v`, `‖z‖ ≤ v/(|g| − |E|)`. Exact, not first order.

**For the wire.** With `‖Vᴴ x‖ ≤ ‖D‖ ‖x‖`, a light eigenstate of energy `E` has
`‖z‖/‖x‖ ≤ ‖D‖/(|y| − |E|)`. So an allowed leakage `L` (weight off the kernel) holds once
`‖D‖ ≤ √(L/(1 − L)) (|y| − |E|)`. The full two-wall check (absolute event clock, PMAction REVIEW extensions) gives leakage
`≈ 1.1 (K_f/|y|)²` for the heavy state, within this bound. So "`K_f ≪ |y|`" becomes: the largest flip
on either wall is at most `√(L/(1−L))` times the gap, for the leakage `L` one accepts.
-/

namespace PMAction.LightLeakage
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **A symmetric map with `G² = g²` scales every norm by `|g|`.** -/
theorem norm_map_of_sq (G : H →ₗ[ℂ] H) (hG : G.IsSymmetric) (g : ℝ)
    (hsq : ∀ z, G (G z) = ((g ^ 2 : ℝ) : ℂ) • z) (z : H) : ‖G z‖ = |g| * ‖z‖ := by
  have e : ⟪G z, G z⟫_ℂ = ((g ^ 2 : ℝ) : ℂ) * ⟪z, z⟫_ℂ := by
    rw [hG z (G z), hsq z, inner_smul_right]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e
  have e2 : ((‖G z‖ ^ 2 : ℝ) : ℂ) = ((g ^ 2 * ‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
    simpa using e
  have h1 : ‖G z‖ ^ 2 = (|g| * ‖z‖) ^ 2 := by
    rw [mul_pow, sq_abs]
    exact Complex.ofReal_injective e2
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    two_ne_zero).mp h1

/-- **Coercivity of `G − E`.** -/
theorem coercive (G : H →ₗ[ℂ] H) (hG : G.IsSymmetric) (g : ℝ)
    (hsq : ∀ z, G (G z) = ((g ^ 2 : ℝ) : ℂ) • z) (E : ℝ) (z : H) :
    (|g| - |E|) * ‖z‖ ≤ ‖G z - (E : ℂ) • z‖ := by
  have h0 := norm_map_of_sq G hG g hsq z
  have h1 : ‖G z‖ ≤ ‖G z - (E : ℂ) • z‖ + ‖(E : ℂ) • z‖ := by
    calc ‖G z‖ = ‖(G z - (E : ℂ) • z) + (E : ℂ) • z‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have h2 : ‖(E : ℂ) • z‖ = |E| * ‖z‖ := by
    rw [norm_smul]; simp
  rw [h0, h2] at h1
  nlinarith

/-- **The leakage bound**: a light eigenstate's gapped part is at most `v/(|g| − |E|)`. -/
theorem leakage_bound (G : H →ₗ[ℂ] H) (hG : G.IsSymmetric) (g : ℝ)
    (hsq : ∀ z, G (G z) = ((g ^ 2 : ℝ) : ℂ) • z) (E : ℝ) (z w : H)
    (hw : G z - (E : ℂ) • z = w) (hE : |E| < |g|) (v : ℝ) (hv : ‖w‖ ≤ v) :
    ‖z‖ ≤ v / (|g| - |E|) := by
  rw [le_div_iff₀ (by linarith)]
  have h := coercive G hG g hsq E z
  rw [hw] at h
  linarith [mul_comm ‖z‖ (|g| - |E|)]

end PMAction.LightLeakage
