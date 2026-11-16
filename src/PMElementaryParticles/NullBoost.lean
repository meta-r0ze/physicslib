import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The massless measure `d³k/|k|` is invariant under boosts

A massless leg with spatial momentum `k` has energy `|k|`. A boost of rapidity along axis `0`
(`γ > 0`, `|β| < 1`, `γ²(1 − β²) = 1`) sends the null vector `(|k|, k)` to `(|k'|, k')` with
`k' = boost k = (γ(k₀ + β|k|), k₁, k₂)` and `|k'| = γ(|k| + β k₀)` (`nrm_boost`).

* `boost_inv`: the boost with `−β` undoes it, so `boost` is a bijection of `ℝ³ \ {0}`.
* `boost_hasFDerivAt`, `det_J`: its Jacobian determinant is `γ(1 + β k₀/|k|) = |k'|/|k|`.
* `measure_invariant`: so for every `f`, `∫ f(boost k) d³k/|k| = ∫ f(k) d³k/|k|` (change of
  variables, `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`; no integrability
  hypothesis is needed).

This is the Lorentz invariance of the massless leg's measure `d³k/(2|k|)` for boosts along the
pair's momentum, which is the frame transport `PairTransport` and
`MassiveDaughterSpectrum.pair_density` use (there `q = p − p_e` lies along axis `0`).
-/

noncomputable section
open MeasureTheory Set
namespace PMElementaryParticles.NullBoost

/-- Euclidean length on `Fin 3 → ℝ`. -/
def nrm (v : Fin 3 → ℝ) : ℝ := Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)

/-- The boost along axis `0` acting on a massless leg's spatial momentum. -/
def boost (γ β : ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ := ![γ * (v 0 + β * nrm v), v 1, v 2]

lemma nrm_sq (v : Fin 3 → ℝ) : nrm v ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma nrm_nonneg (v : Fin 3 → ℝ) : 0 ≤ nrm v := Real.sqrt_nonneg _

lemma abs_le_nrm (v : Fin 3 → ℝ) : |v 0| ≤ nrm v :=
  Real.abs_le_sqrt (by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)])

lemma nrm_pos {v : Fin 3 → ℝ} (hv : v ≠ 0) : 0 < nrm v := by
  apply Real.sqrt_pos.mpr
  by_contra h
  push Not at h
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h2 : v 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  exact hv (funext fun i => by fin_cases i <;> assumption)

variable {γ β : ℝ}

/-- The boosted leg's energy: `|k'| = γ(|k| + β k₀)`. -/
theorem nrm_boost (hγ : 0 < γ) (hβ : |β| < 1) (h : γ ^ 2 * (1 - β ^ 2) = 1)
    (v : Fin 3 → ℝ) : nrm (boost γ β v) = γ * (nrm v + β * v 0) := by
  have hr := nrm_sq v
  have hpos : 0 ≤ nrm v + β * v 0 := by
    have h1 := abs_le_nrm v
    have h2 : |β * v 0| ≤ nrm v := by
      rw [abs_mul]; nlinarith [abs_nonneg (v 0), abs_nonneg β]
    linarith [neg_abs_le (β * v 0)]
  have hsq : (γ * (v 0 + β * nrm v)) ^ 2 + v 1 ^ 2 + v 2 ^ 2 = (γ * (nrm v + β * v 0)) ^ 2 := by
    linear_combination (-1 : ℝ) * hr + (v 0 ^ 2 - nrm v ^ 2) * h
  show Real.sqrt ((γ * (v 0 + β * nrm v)) ^ 2 + v 1 ^ 2 + v 2 ^ 2) = _
  rw [hsq, Real.sqrt_sq (by positivity)]

theorem boost_inv (hγ : 0 < γ) (hβ : |β| < 1) (h : γ ^ 2 * (1 - β ^ 2) = 1)
    (v : Fin 3 → ℝ) : boost γ (-β) (boost γ β v) = v := by
  have hn := nrm_boost hγ hβ h v
  funext i
  fin_cases i
  · show γ * (boost γ β v 0 + (-β) * nrm (boost γ β v)) = v 0
    rw [hn]
    show γ * (γ * (v 0 + β * nrm v) + (-β) * (γ * (nrm v + β * v 0))) = v 0
    linear_combination v 0 * h
  · simp [boost]
  · simp [boost]

lemma boost_ne_zero (hγ : 0 < γ) (hβ : |β| < 1) (h : γ ^ 2 * (1 - β ^ 2) = 1)
    {v : Fin 3 → ℝ} (hv : v ≠ 0) : boost γ β v ≠ 0 := by
  intro h0
  apply hv
  rw [← boost_inv hγ hβ h v, h0]
  funext i; fin_cases i <;> simp [boost, nrm]

/-- The Jacobian matrix of the boost at `v ≠ 0`. -/
def J (γ β : ℝ) (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![γ * (1 + β * v 0 / nrm v), γ * β * v 1 / nrm v, γ * β * v 2 / nrm v;
     0, 1, 0;
     0, 0, 1]

theorem det_J (v : Fin 3 → ℝ) : (J γ β v).det = γ * (1 + β * v 0 / nrm v) := by
  simp [J, Matrix.det_fin_three]

/-- Coordinate projection. -/
abbrev P (i : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i

theorem boost_hasFDerivAt {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    HasFDerivAt (boost γ β) (Matrix.toLin' (J γ β v)).toContinuousLinearMap v := by
  have hn := nrm_pos hv
  have hs : HasFDerivAt (fun w : Fin 3 → ℝ => w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2)
      ((2 * v 0) • P 0 + (2 * v 1) • P 1 + (2 * v 2) • P 2) v := by
    have h0 := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) v).pow 2
    have h1 := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) v).pow 2
    have h2 := (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) v).pow 2
    convert (h0.add h1).add h2 using 1
    ext w; simp
  have hsq := hs.sqrt (ne_of_gt (by rw [← nrm_sq v]; positivity))
  refine hasFDerivAt_pi'' (fun i => ?_)
  fin_cases i
  · have hc := ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) v).add (hsq.const_mul β)).const_mul γ
    refine hc.congr_fderiv ?_
    ext w
    simp [J, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]
    unfold nrm at hn ⊢
    field_simp
    ring
  · refine (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) v).congr_fderiv ?_
    ext w; simp [J, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]
  · refine (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) v).congr_fderiv ?_
    ext w; simp [J, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]

/-- **The massless measure `d³k/|k|` is boost invariant.** -/
theorem measure_invariant (hγ : 0 < γ) (hβ : |β| < 1) (h : γ ^ 2 * (1 - β ^ 2) = 1)
    (f : (Fin 3 → ℝ) → ℝ) :
    ∫ v, f (boost γ β v) / nrm v = ∫ v, f v / nrm v := by
  have hβ' : |-β| < 1 := by rwa [abs_neg]
  have h' : γ ^ 2 * (1 - (-β) ^ 2) = 1 := by rwa [neg_sq]
  set s : Set (Fin 3 → ℝ) := {0}ᶜ
  have hs : MeasurableSet s := (measurableSet_singleton 0).compl
  have himage : boost γ β '' s = s := by
    ext w; constructor
    · rintro ⟨v, hv, rfl⟩; exact boost_ne_zero hγ hβ h hv
    · intro hw
      exact ⟨boost γ (-β) w, boost_ne_zero hγ hβ' h' hw, by
        have := boost_inv hγ hβ' h' w; rw [neg_neg] at this; exact this⟩
  have hinj : InjOn (boost γ β) s := fun a _ b _ hab => by
    rw [← boost_inv hγ hβ h a, ← boost_inv hγ hβ h b, hab]
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun v hv => (boost_hasFDerivAt (γ := γ) (β := β) hv).hasFDerivWithinAt) hinj
    (fun w => f w / nrm w)
  rw [himage] at hcv
  simp only [s, restrict_compl_singleton] at hcv
  rw [hcv]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ v ∂(volume : Measure (Fin 3 → ℝ)), v ≠ 0 := by
    rw [ae_iff]; simp only [not_not, ofPred_eq_eq_singleton]; exact measure_singleton 0
  filter_upwards [hae] with v hv
  have hn := nrm_pos hv
  have hb := nrm_boost hγ hβ h v
  have hbpos : 0 < nrm (boost γ β v) := nrm_pos (boost_ne_zero hγ hβ h hv)
  rw [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin', det_J, smul_eq_mul]
  have hdet : γ * (1 + β * v 0 / nrm v) = nrm (boost γ β v) / nrm v := by
    rw [hb]; field_simp
  rw [hdet, abs_of_pos (div_pos hbpos hn)]
  field_simp

/-- **The two-leg measure `d³k/|k| d³k̄/|k̄|` is boost invariant**, as an iterated integral (no
integrability hypothesis): boosting both legs of any pair functional leaves it unchanged. With
`G` a function of the pair's total four-momentum, this is the invariance the pair transport uses. -/
theorem pair_invariant (hγ : 0 < γ) (hβ : |β| < 1) (h : γ ^ 2 * (1 - β ^ 2) = 1)
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ) :
    ∫ k, (∫ kb, F (boost γ β k) (boost γ β kb) / nrm kb) / nrm k =
      ∫ k, (∫ kb, F k kb / nrm kb) / nrm k := by
  have hin : ∀ k, ∫ kb, F (boost γ β k) (boost γ β kb) / nrm kb =
      ∫ kb, F (boost γ β k) kb / nrm kb := fun k =>
    measure_invariant hγ hβ h (F (boost γ β k))
  simp only [hin]
  exact measure_invariant hγ hβ h (fun x => ∫ kb, F x kb / nrm kb)

end PMElementaryParticles.NullBoost
