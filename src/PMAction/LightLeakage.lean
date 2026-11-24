import Mathlib.Analysis.InnerProductSpace.Spectrum

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

/-- Error of the zero-energy Schur operator on the light component of a
full eigenstate. The gapped block has constant squared gap, so its inverse
is `G/g²`. The relative residual coefficient is
`v*w / (|g|*(|g|-|E|))`, with `v` and `w` bounding the two directions of
the light–gapped coupling. -/
theorem schur_residual_bound {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (G : H →ₗ[ℂ] H) (hG : G.IsSymmetric) (g : ℝ)
    (hsq : ∀ z, G (G z) = ((g ^ 2 : ℝ) : ℂ) • z)
    (V : H →ₗ[ℂ] L) (W : L →ₗ[ℂ] H) (v w : ℝ) (hv0 : 0 ≤ v)
    (hv : ∀ u, ‖V u‖ ≤ v * ‖u‖) (hw : ∀ u, ‖W u‖ ≤ w * ‖u‖)
    (E : ℝ) (hE : |E| < |g|) (x : L) (z : H)
    (hLight : V z = (E : ℂ) • x) (hGap : G z - (E : ℂ) • z = -W x) :
    ‖(-((g ^ 2 : ℝ) : ℂ)⁻¹) • V (G (W x)) - (E : ℂ) • x‖ ≤
      (v * w / (|g| * (|g| - |E|))) * |E| * ‖x‖ := by
  have hg : 0 < |g| := (abs_nonneg E).trans_lt hE
  have hGap' : W x = (E : ℂ) • z - G z := by
    rw [← neg_eq_iff_eq_neg] at hGap
    rw [← hGap, neg_sub]
  have hscalar : ((g ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 2 (abs_pos.mp hg))
  have hResidual :
      (-((g ^ 2 : ℝ) : ℂ)⁻¹) • V (G (W x)) - (E : ℂ) • x =
        (-(E : ℂ) / ((g ^ 2 : ℝ) : ℂ)) • V (G z) := by
    rw [hGap', map_sub, map_smul, hsq, map_sub, map_smul, map_smul, ← hLight]
    have hcancel : (-((g ^ 2 : ℝ) : ℂ)⁻¹) * ((g ^ 2 : ℝ) : ℂ) = -1 := by
      rw [neg_mul, inv_mul_cancel₀ hscalar]
    simp only [smul_sub, smul_smul, hcancel, neg_one_smul, sub_neg_eq_add, add_sub_cancel_right]
    rw [div_eq_mul_inv, neg_mul, neg_mul, mul_comm (((g ^ 2 : ℝ) : ℂ)⁻¹)]
  have hz : ‖z‖ ≤ w * ‖x‖ / (|g| - |E|) :=
    leakage_bound G hG g hsq E z (-W x) hGap hE (w * ‖x‖) (by simpa using hw x)
  have hd : 0 < |g| - |E| := sub_pos.mpr hE
  have hNorm : ‖(-(E : ℂ) / ((g ^ 2 : ℝ) : ℂ))‖ = |E| / |g| ^ 2 := by
    simp
  rw [hResidual, norm_smul, hNorm]
  calc
    _ ≤ (|E| / |g| ^ 2) * (v * (|g| * ‖z‖)) := by
      rw [← norm_map_of_sq G hG g hsq]
      exact mul_le_mul_of_nonneg_left (hv _) (by positivity)
    _ ≤ (|E| / |g| ^ 2) * (v * (|g| * (w * ‖x‖ / (|g| - |E|)))) := by
      gcongr
    _ = _ := by field_simp [hg.ne', hd.ne']

/-- A residual of size at most `err * ‖x‖` on a nonzero vector puts an
eigenvalue of a finite symmetric operator within `err` of the trial energy. -/
theorem eigenvalue_near_residual {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    [FiniteDimensional ℂ L] {n : ℕ} (hn : Module.finrank ℂ L = n)
    (S : L →ₗ[ℂ] L) (hS : S.IsSymmetric) (E err : ℝ) (herr : 0 ≤ err)
    (x : L) (hx : x ≠ 0) (hres : ‖S x - (E : ℂ) • x‖ ≤ err * ‖x‖) :
    ∃ i : Fin n, |hS.eigenvalues hn i - E| ≤ err := by
  let basis := hS.eigenvectorBasis hn
  have hCoord (i : Fin n) :
      basis.repr (S x - (E : ℂ) • x) i =
        ((hS.eigenvalues hn i - E : ℝ) : ℂ) * basis.repr x i := by
    simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Complex.ofReal_sub, sub_mul]
    rw [show basis.repr (S x) i = _ from hS.eigenvectorBasis_apply_self_apply hn x i]
    rfl
  by_contra! h
  have hSome : ∃ i : Fin n, basis.repr x i ≠ 0 := by
    by_contra! hz
    apply hx
    apply basis.repr.injective
    ext i
    simp [hz i]
  obtain ⟨j, hj⟩ := hSome
  have hTerm (i : Fin n) :
      ‖basis.repr (S x - (E : ℂ) • x) i‖ ^ 2 =
        |hS.eigenvalues hn i - E| ^ 2 * ‖basis.repr x i‖ ^ 2 := by
    rw [hCoord, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hSum : ∑ i, err ^ 2 * ‖basis.repr x i‖ ^ 2 <
      ∑ i, ‖basis.repr (S x - (E : ℂ) • x) i‖ ^ 2 := by
    apply Finset.sum_lt_sum
    · intro i _
      rw [hTerm]
      gcongr
      exact (h i).le
    · refine ⟨j, Finset.mem_univ _, ?_⟩
      rw [hTerm]
      exact mul_lt_mul_of_pos_right (by
        nlinarith [h j, sq_nonneg (|hS.eigenvalues hn j - E| - err)])
        (by positivity)
  rw [← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq,
    basis.repr.norm_map, basis.repr.norm_map] at hSum
  have hSq := pow_le_pow_left₀ (norm_nonneg _) hres 2
  rw [mul_pow] at hSq
  exact (not_lt_of_ge hSq) hSum

/-- Every full light eigenstate lies within a controlled relative error of
the zero-energy Schur spectrum. The adjoint relation ensures that the
Schur operator is symmetric. This estimate tracks individual energies. -/
theorem schur_eigenvalue_near {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    [FiniteDimensional ℂ L] {n : ℕ} (hn : Module.finrank ℂ L = n)
    (G : H →ₗ[ℂ] H) (hG : G.IsSymmetric) (g : ℝ)
    (hsq : ∀ z, G (G z) = ((g ^ 2 : ℝ) : ℂ) • z)
    (V : H →ₗ[ℂ] L) (W : L →ₗ[ℂ] H)
    (hAdj : ∀ z x, ⟪V z, x⟫_ℂ = ⟪z, W x⟫_ℂ)
    (v w : ℝ) (hv0 : 0 ≤ v) (hw0 : 0 ≤ w)
    (hv : ∀ u, ‖V u‖ ≤ v * ‖u‖) (hw : ∀ u, ‖W u‖ ≤ w * ‖u‖)
    (E : ℝ) (hE : |E| < |g|) (x : L) (z : H) (hx : x ≠ 0)
    (hLight : V z = (E : ℂ) • x) (hGap : G z - (E : ℂ) • z = -W x) :
    let S := (-((g ^ 2 : ℝ) : ℂ)⁻¹) • (V.comp (G.comp W))
    ∃ hS : S.IsSymmetric, ∃ i : Fin n,
      |hS.eigenvalues hn i - E| ≤ (v * w / (|g| * (|g| - |E|))) * |E| := by
  intro S
  have hS : S.IsSymmetric := by
    intro a b
    simp only [S, LinearMap.smul_apply, LinearMap.comp_apply, inner_smul_left, inner_smul_right]
    rw [hAdj, hG]
    have hReverse := congrArg star (hAdj (G (W b)) a)
    have hInner : ⟪W a, G (W b)⟫_ℂ = ⟪a, V (G (W b))⟫_ℂ := by
      simpa [inner_conj_symm] using hReverse.symm
    rw [hInner]
    simp
  refine ⟨hS, eigenvalue_near_residual hn S hS E _ ?_ x hx ?_⟩
  · have := sub_pos.mpr hE
    positivity
  · exact schur_residual_bound G hG g hsq V W v w hv0 hv hw E hE x z hLight hGap

end PMAction.LightLeakage
