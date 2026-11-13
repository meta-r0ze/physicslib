import PMAction.PolarizationAverage

/-!
# The continuum shell's angular moments match the D₄ roots'

`PolarizationAverage.orbital_third` averages the polarization integrand's `q²` part over the 24
D₄ roots. The shell `μ < |k| < M` of `LeadingLog` is a continuum integral. This module shows
the two agree: over the shell, the integrand's angular moments up to degree four are the
isotropic ones, the same as the roots' (`D4Isotropy.second_moment`, `fourth_moment`).

* `iso_inv`: an isometry of momentum space preserves shell integrals.
* `diag`: a reflection carries any `x` to `|x| e₀`, so `∫ (k·x)ⁿ |k|⁻ᵐ = |x|ⁿ ∫ k₀ⁿ |k|⁻ᵐ`.
* `quad_form`, `quartic_form`, `mixed_form`: by polarization, the second and fourth moment
  tensors are `C δ` and `(A/3)(δδ + δδ + δδ)`.
* `C_eq`, `A_eq`: tracing, `C = L/4` and `A = L/8` with `L = ∫ |k|⁻⁴`: the continuum
  direction average is the D₄ one (`¼` and `1/24`).
* `shell_orbital`: the shell integral of the polarization integrand's `q²` part is
  `−(1/3)(q²δ_μν − q_μq_ν) · 2π² ln(M/μ)`.
* `shell_eq_root_average`: it is the D₄ root average of the same integrand times `∫ |k|⁻⁴`.
-/

noncomputable section
namespace PMAction.ShellMoments
open Real MeasureTheory Set D4Gauge LeadingLog PolarizationAverage

variable {lo hi : ℝ}

/-- The unit vector along coordinate `i`. -/
abbrev bv (i : Fin 4) : Mom := EuclideanSpace.single i (1 : ℝ)

lemma inner_bv (k : Mom) (i : Fin 4) : inner ℝ k (bv i) = k i := by
  simp [bv, EuclideanSpace.inner_single_right]

lemma bv_inner (q : Mom) (i : Fin 4) : inner ℝ (bv i) q = q i := by
  simp [bv, EuclideanSpace.inner_single_left]

lemma norm_bv (i : Fin 4) : ‖bv i‖ = 1 := by simp [bv]

lemma bv_bv (i j : Fin 4) : inner ℝ (bv i) (bv j) = d i j := by
  rw [bv_inner]
  by_cases h : i = j
  · subst h; simp [bv, d]
  · simp [bv, d, h]

/-- Polynomial-times-radial integrands are integrable on the shell. -/
lemma ion (hlo : 0 < lo) (P : Mom → ℝ) (hP : Continuous P) (m : ℕ) :
    IntegrableOn (fun k => P k * ‖k‖⁻¹ ^ m) (shell lo hi) := by
  have hK : IsCompact (Metric.closedBall (0 : Mom) hi ∩ {k | lo ≤ ‖k‖}) :=
    (isCompact_closedBall 0 hi).inter_right (isClosed_le continuous_const continuous_norm)
  have hsub : shell lo hi ⊆ Metric.closedBall (0 : Mom) hi ∩ {k | lo ≤ ‖k‖} := fun k hk => by
    simp only [shell, Set.mem_preimage, Set.mem_Ioo] at hk
    exact ⟨mem_closedBall_zero_iff.2 hk.2.le, hk.1.le⟩
  refine (ContinuousOn.integrableOn_compact hK ?_).mono_set hsub
  refine hP.continuousOn.mul ((continuous_norm.continuousOn.inv₀ fun k hk => ?_).pow m)
  exact (lt_of_lt_of_le hlo hk.2).ne'

lemma lin2 {f g : Mom → ℝ} (hf : IntegrableOn f (shell lo hi)) (hg : IntegrableOn g (shell lo hi))
    (a b : ℝ) :
    ∫ k in shell lo hi, (a * f k + b * g k) =
      a * (∫ k in shell lo hi, f k) + b * ∫ k in shell lo hi, g k := by
  rw [integral_add (Integrable.const_mul hf a) (Integrable.const_mul hg b), integral_const_mul,
    integral_const_mul]

lemma lin4 {f g h l : Mom → ℝ} (hf : IntegrableOn f (shell lo hi))
    (hg : IntegrableOn g (shell lo hi)) (hh : IntegrableOn h (shell lo hi))
    (hl : IntegrableOn l (shell lo hi)) (a b c e : ℝ) :
    ∫ k in shell lo hi, (a * f k + b * g k + c * h k + e * l k) =
      a * (∫ k in shell lo hi, f k) + b * (∫ k in shell lo hi, g k) +
        c * (∫ k in shell lo hi, h k) + e * ∫ k in shell lo hi, l k := by
  have h1 := Integrable.const_mul hf a
  have h2 := Integrable.const_mul hg b
  have h3 := Integrable.const_mul hh c
  have h4 := Integrable.const_mul hl e
  rw [integral_add (f := fun k => a * f k + b * g k + c * h k) ((h1.add h2).add h3) h4,
    integral_add (f := fun k => a * f k + b * g k) (h1.add h2) h3, integral_add h1 h2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

lemma lin5 {f g h l p : Mom → ℝ} (hf : IntegrableOn f (shell lo hi))
    (hg : IntegrableOn g (shell lo hi)) (hh : IntegrableOn h (shell lo hi))
    (hl : IntegrableOn l (shell lo hi)) (hp : IntegrableOn p (shell lo hi)) (a b c e r : ℝ) :
    ∫ k in shell lo hi, (a * f k + b * g k + c * h k + e * l k + r * p k) =
      a * (∫ k in shell lo hi, f k) + b * (∫ k in shell lo hi, g k) +
        c * (∫ k in shell lo hi, h k) + e * (∫ k in shell lo hi, l k) +
          r * ∫ k in shell lo hi, p k := by
  have h1 := Integrable.const_mul hf a
  have h2 := Integrable.const_mul hg b
  have h3 := Integrable.const_mul hh c
  have h4 := Integrable.const_mul hl e
  have h5 := Integrable.const_mul hp r
  rw [integral_add (f := fun k => a * f k + b * g k + c * h k + e * l k)
      (((h1.add h2).add h3).add h4) h5,
    integral_add (f := fun k => a * f k + b * g k + c * h k) ((h1.add h2).add h3) h4,
    integral_add (f := fun k => a * f k + b * g k) (h1.add h2) h3, integral_add h1 h2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]

/-- **Isometry invariance.** -/
theorem iso_inv (T : Mom ≃ₗᵢ[ℝ] Mom) (F : Mom → ℝ) :
    ∫ k in shell lo hi, F (T k) = ∫ k in shell lo hi, F k := by
  have hS : MeasurableSet (shell lo hi) := measurable_norm measurableSet_Ioo
  rw [← integral_indicator hS, ← integral_indicator hS]
  have e : (shell lo hi).indicator (fun k => F (T k)) =
      fun k => (shell lo hi).indicator F (T k) := by
    funext k
    simp only [Set.indicator, shell, Set.mem_preimage, LinearIsometryEquiv.norm_map]
  rw [e]
  exact (T.measurePreserving).integral_comp T.toHomeomorph.measurableEmbedding _

/-- **The diagonal moments.** A reflection carries `x` to `|x| e₀`. -/
theorem diag (x : Mom) (n m : ℕ) :
    ∫ k in shell lo hi, inner ℝ k x ^ n * ‖k‖⁻¹ ^ m =
      ‖x‖ ^ n * ∫ k in shell lo hi, k 0 ^ n * ‖k‖⁻¹ ^ m := by
  have hy : ‖x‖ = ‖‖x‖ • bv 0‖ := by rw [norm_smul, norm_bv, mul_one, norm_norm]
  have hT := Submodule.reflection_sub hy
  set T := (Submodule.span ℝ {x - ‖x‖ • bv 0})ᗮ.reflection
  have h1 : ∀ k, inner ℝ k x = inner ℝ (T k) (‖x‖ • bv 0) := fun k => by
    rw [← hT, LinearIsometryEquiv.inner_map_map]
  have h2 : ∀ k : Mom, inner ℝ k (‖x‖ • bv 0) = ‖x‖ * k 0 := fun k => by
    rw [real_inner_smul_right, inner_bv]
  calc ∫ k in shell lo hi, inner ℝ k x ^ n * ‖k‖⁻¹ ^ m
      = ∫ k in shell lo hi, (fun k => inner ℝ k (‖x‖ • bv 0) ^ n * ‖k‖⁻¹ ^ m) (T k) := by
        congr 1; funext k; simp only [h1, LinearIsometryEquiv.norm_map]
    _ = ∫ k in shell lo hi, inner ℝ k (‖x‖ • bv 0) ^ n * ‖k‖⁻¹ ^ m :=
        iso_inv T (fun k => inner ℝ k (‖x‖ • bv 0) ^ n * ‖k‖⁻¹ ^ m)
    _ = ∫ k in shell lo hi, ‖x‖ ^ n * (k 0 ^ n * ‖k‖⁻¹ ^ m) := by
        congr 1; funext k; rw [h2, mul_pow, mul_assoc]
    _ = _ := integral_const_mul _ _

/-- **The second moment tensor.** `∫ (k·u)(k·v)|k|⁻⁶ = C ⟨u, v⟩`. -/
theorem quad_form (hlo : 0 < lo) (u v : Mom) :
    ∫ k in shell lo hi, inner ℝ k u * inner ℝ k v * ‖k‖⁻¹ ^ 6 =
      (∫ k in shell lo hi, k 0 ^ 2 * ‖k‖⁻¹ ^ 6) * inner ℝ u v := by
  have e : ∀ k : Mom, inner ℝ k u * inner ℝ k v * ‖k‖⁻¹ ^ 6 =
      1 / 4 * (inner ℝ k (u + v) ^ 2 * ‖k‖⁻¹ ^ 6) +
        (-1 / 4) * (inner ℝ k (u - v) ^ 2 * ‖k‖⁻¹ ^ 6) := fun k => by
    rw [inner_add_right, inner_sub_right]; ring
  simp_rw [e]
  rw [lin2 (ion hlo (fun k => inner ℝ k (u + v) ^ 2) (by fun_prop) 6)
    (ion hlo (fun k => inner ℝ k (u - v) ^ 2) (by fun_prop) 6), diag, diag,
    norm_add_sq_real, norm_sub_sq_real]
  ring

/-- **The fourth moment, two directions.** `∫ (k·u)²(k·v)²|k|⁻⁸ = (A/3)(|u|²|v|² + 2⟨u,v⟩²)`. -/
theorem quartic_form (hlo : 0 < lo) (u v : Mom) :
    ∫ k in shell lo hi, inner ℝ k u ^ 2 * inner ℝ k v ^ 2 * ‖k‖⁻¹ ^ 8 =
      (∫ k in shell lo hi, k 0 ^ 4 * ‖k‖⁻¹ ^ 8) / 3 *
        (‖u‖ ^ 2 * ‖v‖ ^ 2 + 2 * inner ℝ u v ^ 2) := by
  have e : ∀ k : Mom, inner ℝ k u ^ 2 * inner ℝ k v ^ 2 * ‖k‖⁻¹ ^ 8 =
      1 / 12 * (inner ℝ k (u + v) ^ 4 * ‖k‖⁻¹ ^ 8) +
        1 / 12 * (inner ℝ k (u - v) ^ 4 * ‖k‖⁻¹ ^ 8) +
          (-1 / 6) * (inner ℝ k u ^ 4 * ‖k‖⁻¹ ^ 8) +
            (-1 / 6) * (inner ℝ k v ^ 4 * ‖k‖⁻¹ ^ 8) := fun k => by
    rw [inner_add_right, inner_sub_right]; ring
  simp_rw [e]
  rw [lin4 (ion hlo (fun k => inner ℝ k (u + v) ^ 4) (by fun_prop) 8)
    (ion hlo (fun k => inner ℝ k (u - v) ^ 4) (by fun_prop) 8)
    (ion hlo (fun k => inner ℝ k u ^ 4) (by fun_prop) 8)
    (ion hlo (fun k => inner ℝ k v ^ 4) (by fun_prop) 8), diag, diag, diag, diag,
    show ‖u + v‖ ^ 4 = (‖u + v‖ ^ 2) ^ 2 by ring, show ‖u - v‖ ^ 4 = (‖u - v‖ ^ 2) ^ 2 by ring,
    norm_add_sq_real, norm_sub_sq_real]
  ring

/-- **The fourth moment, mixed.**
`∫ (k·u)(k·v)(k·q)²|k|⁻⁸ = (A/3)(⟨u,v⟩|q|² + 2⟨u,q⟩⟨v,q⟩)`. -/
theorem mixed_form (hlo : 0 < lo) (u v q : Mom) :
    ∫ k in shell lo hi, inner ℝ k u * inner ℝ k v * inner ℝ k q ^ 2 * ‖k‖⁻¹ ^ 8 =
      (∫ k in shell lo hi, k 0 ^ 4 * ‖k‖⁻¹ ^ 8) / 3 *
        (inner ℝ u v * ‖q‖ ^ 2 + 2 * inner ℝ u q * inner ℝ v q) := by
  have e : ∀ k : Mom, inner ℝ k u * inner ℝ k v * inner ℝ k q ^ 2 * ‖k‖⁻¹ ^ 8 =
      1 / 4 * (inner ℝ k (u + v) ^ 2 * inner ℝ k q ^ 2 * ‖k‖⁻¹ ^ 8) +
        (-1 / 4) * (inner ℝ k (u - v) ^ 2 * inner ℝ k q ^ 2 * ‖k‖⁻¹ ^ 8) := fun k => by
    rw [inner_add_right, inner_sub_right]; ring
  simp_rw [e]
  rw [lin2 (ion hlo (fun k => inner ℝ k (u + v) ^ 2 * inner ℝ k q ^ 2) (by fun_prop) 8)
    (ion hlo (fun k => inner ℝ k (u - v) ^ 2 * inner ℝ k q ^ 2) (by fun_prop) 8),
    quartic_form hlo, quartic_form hlo, norm_add_sq_real, norm_sub_sq_real, inner_add_left,
    inner_sub_left]
  ring

/-- **The second-moment constant.** `C = L/4`: each direction carries a quarter. -/
theorem C_eq (hlo : 0 < lo) :
    ∫ k in shell lo hi, k 0 ^ 2 * ‖k‖⁻¹ ^ 6 = 1 / 4 * ∫ k in shell lo hi, ‖k‖⁻¹ ^ 4 := by
  have hpt : ∀ k : Mom, ‖k‖⁻¹ ^ 4 = ∑ i, inner ℝ k (bv i) ^ 2 * ‖k‖⁻¹ ^ 6 := by
    intro k
    rw [← Finset.sum_mul]
    simp only [inner_bv]
    rw [← EuclideanSpace.real_norm_sq_eq]
    rcases eq_or_ne ‖k‖ 0 with h | h
    · rw [h]; simp
    rw [show ‖k‖ ^ 2 * ‖k‖⁻¹ ^ 6 = (‖k‖ * ‖k‖⁻¹) ^ 2 * ‖k‖⁻¹ ^ 4 by ring, mul_inv_cancel₀ h,
      one_pow, one_mul]
  have hterm : ∀ i, ∫ k in shell lo hi, inner ℝ k (bv i) ^ 2 * ‖k‖⁻¹ ^ 6 =
      ∫ k in shell lo hi, k 0 ^ 2 * ‖k‖⁻¹ ^ 6 := fun i => by
    rw [diag, norm_bv, one_pow, one_mul]
  have h4 : ∫ k in shell lo hi, ‖k‖⁻¹ ^ 4 = 4 * ∫ k in shell lo hi, k 0 ^ 2 * ‖k‖⁻¹ ^ 6 := by
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ =>
      ion hlo (fun k => inner ℝ k (bv i) ^ 2) (by fun_prop) 6]
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  linarith

/-- **The fourth-moment constant.** `A = L/8`. -/
theorem A_eq (hlo : 0 < lo) :
    ∫ k in shell lo hi, k 0 ^ 4 * ‖k‖⁻¹ ^ 8 = 1 / 8 * ∫ k in shell lo hi, ‖k‖⁻¹ ^ 4 := by
  have hpt : ∀ k : Mom, ‖k‖⁻¹ ^ 4 =
      ∑ i, ∑ j, inner ℝ k (bv i) ^ 2 * inner ℝ k (bv j) ^ 2 * ‖k‖⁻¹ ^ 8 := by
    intro k
    have hs : ∑ i, ∑ j, inner ℝ k (bv i) ^ 2 * inner ℝ k (bv j) ^ 2 * ‖k‖⁻¹ ^ 8 =
        (‖k‖ ^ 2) ^ 2 * ‖k‖⁻¹ ^ 8 := by
      simp only [inner_bv, Fin.sum_univ_four]
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
      ring
    rw [hs]
    rcases eq_or_ne ‖k‖ 0 with h | h
    · rw [h]; simp
    rw [show (‖k‖ ^ 2) ^ 2 * ‖k‖⁻¹ ^ 8 = (‖k‖ * ‖k‖⁻¹) ^ 4 * ‖k‖⁻¹ ^ 4 by ring,
      mul_inv_cancel₀ h, one_pow, one_mul]
  have h8 : ∫ k in shell lo hi, ‖k‖⁻¹ ^ 4 = 8 * ∫ k in shell lo hi, k 0 ^ 4 * ‖k‖⁻¹ ^ 8 := by
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      ion hlo (fun k => inner ℝ k (bv i) ^ 2 * inner ℝ k (bv j) ^ 2) (by fun_prop) 8]
    rw [Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ =>
      ion hlo (fun k => inner ℝ k (bv i) ^ 2 * inner ℝ k (bv j) ^ 2) (by fun_prop) 8]
    simp only [quartic_form hlo, norm_bv, bv_bv, one_pow, one_mul]
    simp only [Fin.sum_univ_four, d]
    norm_num
    ring
  linarith

/-- The continuum `q²` part of the polarization integrand (`PolarizationAverage.coef`). -/
def coefC (q : Mom) (μ ν : Fin 4) (k : Mom) : ℝ :=
  4 * (k μ * k ν) * (-‖q‖ ^ 2 * ‖k‖⁻¹ ^ 6 + 4 * inner ℝ k q ^ 2 * ‖k‖⁻¹ ^ 8)
    - 4 * (k μ * q ν + q μ * k ν) * inner ℝ k q * ‖k‖⁻¹ ^ 6 + q μ * q ν * ‖k‖⁻¹ ^ 4

/-- **The shell's orbital `−1/3`.** -/
theorem shell_orbital (hlo : 0 < lo) (hlh : lo ≤ hi) (q : Mom) (μ ν : Fin 4) :
    ∫ k in shell lo hi, coefC q μ ν k =
      -(1 / 3) * (‖q‖ ^ 2 * d μ ν - q μ * q ν) * (2 * π ^ 2 * Real.log (hi / lo)) := by
  have e : ∀ k : Mom, coefC q μ ν k =
      (-4 * ‖q‖ ^ 2) * (inner ℝ k (bv μ) * inner ℝ k (bv ν) * ‖k‖⁻¹ ^ 6) +
        16 * (inner ℝ k (bv μ) * inner ℝ k (bv ν) * inner ℝ k q ^ 2 * ‖k‖⁻¹ ^ 8) +
          (-4 * q ν) * (inner ℝ k (bv μ) * inner ℝ k q * ‖k‖⁻¹ ^ 6) +
            (-4 * q μ) * (inner ℝ k (bv ν) * inner ℝ k q * ‖k‖⁻¹ ^ 6) +
              (q μ * q ν) * (1 * ‖k‖⁻¹ ^ 4) := fun k => by
    simp only [coefC, inner_bv]; ring
  simp_rw [e]
  rw [lin5 (ion hlo (fun k => inner ℝ k (bv μ) * inner ℝ k (bv ν)) (by fun_prop) 6)
    (ion hlo (fun k => inner ℝ k (bv μ) * inner ℝ k (bv ν) * inner ℝ k q ^ 2) (by fun_prop) 8)
    (ion hlo (fun k => inner ℝ k (bv μ) * inner ℝ k q) (by fun_prop) 6)
    (ion hlo (fun k => inner ℝ k (bv ν) * inner ℝ k q) (by fun_prop) 6)
    (ion hlo (fun _ => (1 : ℝ)) (by fun_prop) 4)]
  simp only [one_mul]
  rw [quad_form hlo, mixed_form hlo, quad_form hlo, quad_form hlo, bv_bv, bv_inner, bv_inner,
    C_eq hlo, A_eq hlo, shell_log hlo hlh]
  ring

lemma inv_quartic_sum : ∑ r ∈ roots, 1 / sq4 (rv r) ^ 2 = 6 := by
  rw [Finset.sum_congr rfl fun r hr => by rw [root_sq hr], Finset.sum_const, roots_card,
    nsmul_eq_mul]
  norm_num

/-- **The shell average is the D₄ root average.** The continuum shell integral of the
polarization integrand's `q²` part equals its average over the 24 roots times `∫ |k|⁻⁴`. -/
theorem shell_eq_root_average (hlo : 0 < lo) (hlh : lo ≤ hi) (q : Mom) (μ ν : Fin 4) :
    ∫ k in shell lo hi, coefC q μ ν k =
      (∑ r ∈ roots, coef (fun i => q i) μ ν r) / (∑ r ∈ roots, 1 / sq4 (rv r) ^ 2) *
        ∫ k in shell lo hi, ‖k‖⁻¹ ^ 4 := by
  rw [shell_orbital hlo hlh, orbital_third, inv_quartic_sum, shell_log hlo hlh,
    show sq4 (fun i => q i) = ‖q‖ ^ 2 from (EuclideanSpace.real_norm_sq_eq q).symm]
  ring

end PMAction.ShellMoments
