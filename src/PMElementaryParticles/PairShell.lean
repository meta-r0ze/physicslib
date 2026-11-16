import PMElementaryParticles.NullBoost
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Shell coordinates for a massless pair: the energy-momentum delta, without a delta

A massless pair with total spatial momentum `P⃗ = b e₀` (`b > 0`) has legs `k` and `k̄ = P⃗ − k`. The
surfaces of fixed pair energy `E = |k| + |P⃗ − k|` are prolate spheroids with foci `0` and `P⃗`. In
the coordinates `(E, ν, φ)`

  `k = Ψ(E, ν, φ) = ((b + E cos ν)/2, (M/2) sin ν cos φ, (M/2) sin ν sin φ)`, `M = √(E² − b²)`,

the legs' energies are `|k| = (E + b cos ν)/2`, `|k̄| = (E − b cos ν)/2` (`nrm_Ψ`, `nrm_Ψ_bar`), and
`(ν, φ)` are exactly the polar angles of `k` in the pair's rest frame (the boost along `e₀` with
`γ = E/M` takes `(M/2)(1, cos ν, sin ν cos φ, sin ν sin φ)` to `(|k|, k)`).

* `det_J`: the Jacobian determinant is `(sin ν/8)(E² − b² cos² ν) = (sin ν/2)|k||k̄|`.
* `shell_integral`: so for every `g`, `∫_{ℝ³} g(k) d³k/(|k||P⃗ − k|) = ∫_S (sin ν/2) g(Ψ(E, ν, φ))`,
  over `S = (b, ∞) × (0, π) × (−π, π)`, with no integrability hypothesis.

So the two-leg measure `d³k/(2|k|) d³k̄/(2|k̄|)` at fixed total momentum, written against the pair
energy `E`, has density `(1/8) dE dΩ*` with `dΩ*` the rest-frame solid angle: the energy delta becomes
the `E`-coordinate, and the pair average at fixed `E` is the isotropic rest-frame average of the
boosted pair, which is what `PairTransport` and `MassiveDaughterSpectrum.pair_density` assume.
-/

noncomputable section
open MeasureTheory Set Real
namespace PMElementaryParticles.PairShell
open PMElementaryParticles.NullBoost

variable {b : ℝ}

/-- Rest-frame pair mass at pair energy `E`. -/
def Mb (b E : ℝ) : ℝ := Real.sqrt (E ^ 2 - b ^ 2)

/-- Shell coordinates `(E, ν, φ) ↦ k`. -/
def Ψ (b : ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(b + p 0 * cos (p 1)) / 2, Mb b (p 0) / 2 * sin (p 1) * cos (p 2),
    Mb b (p 0) / 2 * sin (p 1) * sin (p 2)]

/-- The pair's total spatial momentum. -/
def P (b : ℝ) : Fin 3 → ℝ := ![b, 0, 0]

/-- The coordinate domain. -/
def S (b : ℝ) : Set (Fin 3 → ℝ) :=
  {p | b < p 0 ∧ 0 < p 1 ∧ p 1 < π ∧ -π < p 2 ∧ p 2 < π}

lemma Mb_sq {E : ℝ} (h : b ≤ E) (hb : 0 ≤ b) : Mb b E ^ 2 = E ^ 2 - b ^ 2 :=
  Real.sq_sqrt (by nlinarith)

lemma cos_bound (hb : 0 < b) {E ν : ℝ} (hE : b < E) : |b * cos ν| < E := by
  rw [abs_mul, abs_of_pos hb]
  calc b * |cos ν| ≤ b * 1 := by gcongr; exact abs_cos_le_one ν
    _ < E := by linarith

theorem nrm_Ψ (hb : 0 < b) {p : Fin 3 → ℝ} (hp : b < p 0) :
    nrm (Ψ b p) = (p 0 + b * cos (p 1)) / 2 := by
  have hc := cos_bound hb (ν := p 1) hp
  have hpos : 0 ≤ (p 0 + b * cos (p 1)) / 2 := by linarith [neg_abs_le (b * cos (p 1))]
  have hM := Mb_sq hp.le hb.le
  unfold nrm
  rw [← Real.sqrt_sq hpos]
  congr 1
  simp only [Ψ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have h1 := sin_sq_add_cos_sq (p 1)
  have h2 := sin_sq_add_cos_sq (p 2)
  have e : (Mb b (p 0) / 2 * sin (p 1) * cos (p 2)) ^ 2 + (Mb b (p 0) / 2 * sin (p 1) * sin (p 2)) ^ 2
      = Mb b (p 0) ^ 2 / 4 * sin (p 1) ^ 2 * (sin (p 2) ^ 2 + cos (p 2) ^ 2) := by ring
  rw [add_assoc, e, h2, hM]
  linear_combination ((p 0 ^ 2 - b ^ 2) / 4) * h1

theorem nrm_Ψ_bar (hb : 0 < b) {p : Fin 3 → ℝ} (hp : b < p 0) :
    nrm (P b - Ψ b p) = (p 0 - b * cos (p 1)) / 2 := by
  have hc := cos_bound hb (ν := p 1) hp
  have hpos : 0 ≤ (p 0 - b * cos (p 1)) / 2 := by linarith [le_abs_self (b * cos (p 1))]
  have hM := Mb_sq hp.le hb.le
  unfold nrm
  rw [← Real.sqrt_sq hpos]
  congr 1
  simp only [P, Ψ, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have h1 := sin_sq_add_cos_sq (p 1)
  have h2 := sin_sq_add_cos_sq (p 2)
  have e : (0 - Mb b (p 0) / 2 * sin (p 1) * cos (p 2)) ^ 2 +
      (0 - Mb b (p 0) / 2 * sin (p 1) * sin (p 2)) ^ 2
      = Mb b (p 0) ^ 2 / 4 * sin (p 1) ^ 2 * (sin (p 2) ^ 2 + cos (p 2) ^ 2) := by ring
  rw [add_assoc, e, h2, hM]
  linear_combination ((p 0 ^ 2 - b ^ 2) / 4) * h1

/-- The Jacobian matrix of `Ψ` (columns `E, ν, φ`). -/
def J (b : ℝ) (p : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos (p 1) / 2, -(p 0 * sin (p 1)) / 2, 0;
     p 0 / (2 * Mb b (p 0)) * sin (p 1) * cos (p 2), Mb b (p 0) / 2 * cos (p 1) * cos (p 2),
       -(Mb b (p 0) / 2 * sin (p 1) * sin (p 2));
     p 0 / (2 * Mb b (p 0)) * sin (p 1) * sin (p 2), Mb b (p 0) / 2 * cos (p 1) * sin (p 2),
       Mb b (p 0) / 2 * sin (p 1) * cos (p 2)]

theorem det_J (hb : 0 < b) {p : Fin 3 → ℝ} (hp : b < p 0) :
    (J b p).det = sin (p 1) / 8 * (p 0 ^ 2 - b ^ 2 * cos (p 1) ^ 2) := by
  have hM := Mb_sq hp.le hb.le
  have hMpos : 0 < Mb b (p 0) := Real.sqrt_pos.mpr (by nlinarith)
  have h1 := sin_sq_add_cos_sq (p 1)
  have h2 := sin_sq_add_cos_sq (p 2)
  have hq : p 0 / (2 * Mb b (p 0)) * Mb b (p 0) = p 0 / 2 := by field_simp
  rw [Matrix.det_fin_three]
  simp only [J, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination (Mb b (p 0) ^ 2 / 8 * cos (p 1) ^ 2 * sin (p 1) + p 0 ^ 2 / 8 * sin (p 1) ^ 3) * h2
    + (p 0 * sin (p 1) ^ 3 * (sin (p 2) ^ 2 + cos (p 2) ^ 2) / 4) * hq
    + (sin (p 1) / 8 * cos (p 1) ^ 2) * hM + (p 0 ^ 2 * sin (p 1) / 8) * h1

lemma hasDerivAt_Mb (hb : 0 < b) {E : ℝ} (hE : b < E) :
    HasDerivAt (Mb b) (E / Mb b E) E := by
  have h1 : HasDerivAt (fun E : ℝ => E ^ 2 - b ^ 2) (2 * E) E := by
    simpa [sub_eq_add_neg] using (hasDerivAt_pow 2 E).add_const (-b ^ 2)
  have h2 := h1.sqrt (by nlinarith)
  unfold Mb
  exact h2.congr_deriv (by rw [mul_div_mul_left _ _ (two_ne_zero)])

/-- Coordinate projection. -/
abbrev pr (i : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i

theorem Ψ_hasFDerivAt (hb : 0 < b) {p : Fin 3 → ℝ} (hp : b < p 0) :
    HasFDerivAt (Ψ b) (Matrix.toLin' (J b p)).toContinuousLinearMap p := by
  have hMpos : 0 < Mb b (p 0) := Real.sqrt_pos.mpr (by nlinarith)
  have d0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) p
  have d1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) p
  have d2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) p
  have dc1 := (Real.hasDerivAt_cos (p 1)).comp_hasFDerivAt p d1
  have ds1 := (Real.hasDerivAt_sin (p 1)).comp_hasFDerivAt p d1
  have dc2 := (Real.hasDerivAt_cos (p 2)).comp_hasFDerivAt p d2
  have ds2 := (Real.hasDerivAt_sin (p 2)).comp_hasFDerivAt p d2
  have dM := (hasDerivAt_Mb hb hp).comp_hasFDerivAt p d0
  refine hasFDerivAt_pi'' (fun i => ?_)
  fin_cases i
  · have h := ((d0.mul dc1).const_add b).const_mul (1 / 2 : ℝ)
    have hf : (fun x => Ψ b x 0) = fun x => 1 / 2 * (b + x 0 * cos (x 1)) := by
      funext x; show (b + x 0 * cos (x 1)) / 2 = _; ring
    rw [show (fun x => Ψ b x ((⟨0, by decide⟩ : Fin 3))) = fun x => Ψ b x 0 from rfl, hf]
    refine h.congr_fderiv ?_
    ext w
    simp [J, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]
    ring
  · have h := ((dM.const_mul (1 / 2 : ℝ)).mul ds1).mul dc2
    have hf : (fun x => Ψ b x 1) = fun x => 1 / 2 * Mb b (x 0) * sin (x 1) * cos (x 2) := by
      funext x; show Mb b (x 0) / 2 * sin (x 1) * cos (x 2) = _; ring
    rw [show (fun x => Ψ b x ((⟨1, by decide⟩ : Fin 3))) = fun x => Ψ b x 1 from rfl, hf]
    refine h.congr_fderiv ?_
    ext w
    simp [J, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]
    field_simp
    ring
  · have h := ((dM.const_mul (1 / 2 : ℝ)).mul ds1).mul ds2
    have hf : (fun x => Ψ b x 2) = fun x => 1 / 2 * Mb b (x 0) * sin (x 1) * sin (x 2) := by
      funext x; show Mb b (x 0) / 2 * sin (x 1) * sin (x 2) = _; ring
    rw [show (fun x => Ψ b x ((⟨2, by decide⟩ : Fin 3))) = fun x => Ψ b x 2 from rfl, hf]
    refine h.congr_fderiv ?_
    ext w
    simp [J, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]
    field_simp
    ring

lemma Mb_pos (hb : 0 < b) {E : ℝ} (hE : b < E) : 0 < Mb b E :=
  Real.sqrt_pos.mpr (by nlinarith)

theorem Ψ_injOn (hb : 0 < b) : InjOn (Ψ b) (S b) := by
  intro p hp q hq hpq
  have n1 := nrm_Ψ hb hp.1; have n2 := nrm_Ψ hb hq.1
  have m1 := nrm_Ψ_bar hb hp.1; have m2 := nrm_Ψ_bar hb hq.1
  rw [hpq] at n1 m1
  have hE : p 0 = q 0 := by linarith
  have hc : cos (p 1) = cos (q 1) := by
    have : b * cos (p 1) = b * cos (q 1) := by linarith
    exact mul_left_cancel₀ hb.ne' this
  have hν : p 1 = q 1 := Real.injOn_cos ⟨hp.2.1.le, hp.2.2.1.le⟩ ⟨hq.2.1.le, hq.2.2.1.le⟩ hc
  have hA : 0 < Mb b (p 0) / 2 * sin (p 1) :=
    mul_pos (by linarith [Mb_pos hb hp.1]) (sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2.1)
  have e1 := congrFun hpq 1; have e2 := congrFun hpq 2
  simp only [Ψ, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    at e1 e2
  rw [← hE, ← hν] at e1 e2
  have hcos : cos (p 2) = cos (q 2) := mul_left_cancel₀ hA.ne' e1
  have hsin : sin (p 2) = sin (q 2) := mul_left_cancel₀ hA.ne' e2
  have hφ : p 2 = q 2 := by
    have a1 := Complex.arg_cos_add_sin_mul_I (θ := p 2) ⟨hp.2.2.2.1, hp.2.2.2.2.le⟩
    have a2 := Complex.arg_cos_add_sin_mul_I (θ := q 2) ⟨hq.2.2.2.1, hq.2.2.2.2.le⟩
    rw [← a1, ← a2]
    congr 1
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      hcos, hsin]
  funext i; fin_cases i
  · exact hE
  · exact hν
  · exact hφ

set_option linter.unusedSimpArgs false in
/-- Off the half-plane `{k₂ = 0, k₁ ≤ 0}` every momentum has shell coordinates. -/
theorem Ψ_onto (hb : 0 < b) {k : Fin 3 → ℝ} (hk : k 2 ≠ 0 ∨ 0 < k 1) : k ∈ Ψ b '' S b := by
  set ρ := Real.sqrt (k 1 ^ 2 + k 2 ^ 2) with hρ
  have hρ2 : ρ ^ 2 = k 1 ^ 2 + k 2 ^ 2 := Real.sq_sqrt (by positivity)
  have hρpos : 0 < ρ := by
    apply Real.sqrt_pos.mpr
    rcases hk with h | h
    · have := sq_pos_of_ne_zero h; positivity
    · have := sq_pos_of_pos h; positivity
  set r1 := nrm k with hr1
  set r2 := nrm (P b - k) with hr2
  have hr1sq : r1 ^ 2 = k 0 ^ 2 + ρ ^ 2 := by rw [hr1, nrm_sq, hρ2]; ring
  have hr2sq : r2 ^ 2 = (b - k 0) ^ 2 + ρ ^ 2 := by
    rw [hr2, nrm_sq, hρ2]; simp [P]; ring
  have hr1n : 0 ≤ r1 := nrm_nonneg _
  have hr2n : 0 ≤ r2 := nrm_nonneg _
  have hr1gt : |k 0| < r1 := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt (k 0 ^ 2) < Real.sqrt (r1 ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
      _ = r1 := Real.sqrt_sq hr1n
  have hr2gt : |b - k 0| < r2 := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt ((b - k 0) ^ 2) < Real.sqrt (r2 ^ 2) :=
          Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
      _ = r2 := Real.sqrt_sq hr2n
  have hsum : b < r1 + r2 := by
    have := abs_add_le (k 0) (b - k 0)
    rw [show k 0 + (b - k 0) = b by ring, abs_of_pos hb] at this
    linarith
  have h2k : |2 * k 0 - b| < r1 + r2 := by
    have := abs_sub (k 0) (b - k 0)
    rw [show k 0 - (b - k 0) = 2 * k 0 - b by ring] at this
    linarith
  have hprod : (r1 - r2) * (r1 + r2) = b * (2 * k 0 - b) := by nlinarith
  set c := (r1 - r2) / b with hc
  have hcb : |c| < 1 := by
    rw [hc, abs_div, abs_of_pos hb, div_lt_one hb]
    have hs : 0 < r1 + r2 := by linarith
    have : |r1 - r2| * (r1 + r2) = b * |2 * k 0 - b| := by
      rw [← abs_of_pos hs, ← abs_mul, hprod, abs_mul, abs_of_pos hb]
    nlinarith [abs_nonneg (r1 - r2), abs_nonneg (2 * k 0 - b)]
  have hc1 : -1 < c := by linarith [neg_abs_le c]
  have hc2 : c < 1 := by linarith [le_abs_self c]
  set z : ℂ := ⟨k 1, k 2⟩ with hz
  have hz0 : z ≠ 0 := by
    intro h; rw [Complex.ext_iff] at h; simp [hz] at h
    rcases hk with hk | hk
    · exact hk h.2
    · linarith [h.1]
  have hzn : ‖z‖ = ρ := by
    rw [Complex.norm_def, Complex.normSq_apply, hρ]; congr 1; simp [hz]; ring
  refine ⟨![r1 + r2, Real.arccos c, Complex.arg z], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa using hsum
  · simpa using Real.arccos_pos.mpr hc2
  · simpa using Real.arccos_lt_pi.mpr hc1
  · simpa using Complex.neg_pi_lt_arg z
  · simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    exact Complex.arg_lt_pi_iff.mpr (by
      rcases hk with hk | hk
      · exact Or.inr (by simpa [hz] using hk)
      · exact Or.inl (by simp [hz]; linarith))
  · have hcos : cos (Real.arccos c) = c := Real.cos_arccos hc1.le hc2.le
    have hsin : sin (Real.arccos c) = Real.sqrt (1 - c ^ 2) := Real.sin_arccos c
    have hMsq : Mb b (r1 + r2) ^ 2 = (r1 + r2) ^ 2 - b ^ 2 := Mb_sq hsum.le hb.le
    have hM0 : 0 ≤ Mb b (r1 + r2) := Real.sqrt_nonneg _
    have hS0 : 0 ≤ Real.sqrt (1 - c ^ 2) := Real.sqrt_nonneg _
    have hSsq : Real.sqrt (1 - c ^ 2) ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (by nlinarith)
    -- the transverse size is `ρ`
    have hT : Mb b (r1 + r2) / 2 * Real.sqrt (1 - c ^ 2) = ρ := by
      have hsq : (Mb b (r1 + r2) / 2 * Real.sqrt (1 - c ^ 2)) ^ 2 = ρ ^ 2 := by
        have key : ((r1 + r2) ^ 2 - b ^ 2) * (b ^ 2 - (r1 - r2) ^ 2) = 4 * b ^ 2 * ρ ^ 2 := by
          linear_combination (2 * b ^ 2) * hr1sq + (2 * b ^ 2) * hr2sq
            - ((r1 - r2) * (r1 + r2) + b * (2 * k 0 - b)) * hprod
        rw [mul_pow, div_pow, hMsq, hSsq, hc]
        field_simp
        linear_combination key
      have h0 : 0 ≤ Mb b (r1 + r2) / 2 * Real.sqrt (1 - c ^ 2) := by positivity
      nlinarith [sq_nonneg (Mb b (r1 + r2) / 2 * Real.sqrt (1 - c ^ 2) - ρ),
        sq_nonneg (Mb b (r1 + r2) / 2 * Real.sqrt (1 - c ^ 2) + ρ)]
    have hca : Real.cos (Complex.arg z) = k 1 / ρ := by
      rw [Complex.cos_arg hz0, hzn]
    have hsa : Real.sin (Complex.arg z) = k 2 / ρ := by
      rw [Complex.sin_arg, hzn]
    have h0 : (r1 + r2) * ((r1 - r2) / b) = 2 * k 0 - b := by
      rw [mul_div_assoc', show (r1 + r2) * (r1 - r2) = b * (2 * k 0 - b) by linarith [hprod]]
      field_simp
    funext i; fin_cases i
    · simp only [Ψ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
      rw [hcos, hc, h0]; ring
    · simp only [Ψ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
      rw [hsin, hT, hca]; field_simp
    · simp only [Ψ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
      rw [hsin, hT, hsa]; field_simp

lemma S_measurable : MeasurableSet (S b) := by
  have hc : ∀ i : Fin 3, Continuous fun p : Fin 3 → ℝ => p i := fun i => continuous_apply i
  refine (IsOpen.measurableSet ?_)
  unfold S
  simp only [ofPred_and]
  refine ((isOpen_lt continuous_const (hc 0)).inter ((isOpen_lt continuous_const (hc 1)).inter
    ((isOpen_lt (hc 1) continuous_const).inter ((isOpen_lt continuous_const (hc 2)).inter
      (isOpen_lt (hc 2) continuous_const)))))

lemma image_ae_univ (hb : 0 < b) :
    (Ψ b '' S b : Set (Fin 3 → ℝ)) =ᵐ[volume] (univ : Set (Fin 3 → ℝ)) := by
  rw [ae_eq_univ]
  let H : Submodule ℝ (Fin 3 → ℝ) := LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2)
  have hH : H ≠ ⊤ := by
    intro h
    have : (Pi.single 2 1 : Fin 3 → ℝ) ∈ H := h ▸ Submodule.mem_top
    simp [H] at this
  have hnull : volume (H : Set (Fin 3 → ℝ)) = 0 := Measure.addHaar_submodule volume H hH
  refine measure_mono_null (fun k hk => ?_) hnull
  by_contra hk2
  apply hk
  apply Ψ_onto hb
  by_contra h
  push Not at h
  exact hk2 (by simp [H, h.1])

/-- **The pair measure at fixed total momentum, in shell coordinates.** For every `g`,
`∫ g(k) d³k/(|k||P⃗ − k|) = ∫_S (sin ν/2) g(Ψ(E, ν, φ))`. -/
theorem shell_integral (hb : 0 < b) (g : (Fin 3 → ℝ) → ℝ) :
    ∫ k, g k / (nrm k * nrm (P b - k)) = ∫ p in S b, sin (p 1) / 2 * g (Ψ b p) := by
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume S_measurable
    (fun p hp => (Ψ_hasFDerivAt hb hp.1).hasFDerivWithinAt) (Ψ_injOn hb)
    (fun k => g k / (nrm k * nrm (P b - k)))
  rw [← setIntegral_univ, ← setIntegral_congr_set (image_ae_univ hb), hcv]
  refine setIntegral_congr_fun S_measurable (fun p hp => ?_)
  have hs : 0 < sin (p 1) := sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2.1
  have hc := cos_bound hb (ν := p 1) hp.1
  have hk : 0 < p 0 + b * cos (p 1) := by linarith [neg_abs_le (b * cos (p 1))]
  have hkb : 0 < p 0 - b * cos (p 1) := by linarith [le_abs_self (b * cos (p 1))]
  simp only [smul_eq_mul]
  rw [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin', det_J hb hp.1,
    nrm_Ψ hb hp.1, nrm_Ψ_bar hb hp.1]
  have hdet : sin (p 1) / 8 * (p 0 ^ 2 - b ^ 2 * cos (p 1) ^ 2) =
      sin (p 1) / 8 * ((p 0 + b * cos (p 1)) * (p 0 - b * cos (p 1))) := by ring
  rw [hdet, abs_of_pos (by positivity)]
  field_simp
  ring

end PMElementaryParticles.PairShell
