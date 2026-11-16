import PMElementaryParticles.PolarMeasure
import PMElementaryParticles.MassiveVolume
import PMElementaryParticles.MassiveDaughterSpectrum

/-!
# The massive charged daughter's measure, from the `ℝ³` Lebesgue integral

`MassiveDaughterSpectrum.pair_density` writes the decay density as
`1/(2m) · (P/(4π²)) · 64 G² ⟨pair⟩` with `P = √(E² − μ²)`; the factor `P/(4π²)` was the
supplied "electron measure" (`PolarMeasure.electron_measure_from_integral` derived only its massless
value `E/(4π²)`). Here it is derived for a massive daughter.

* `massive_lorentz_measure`: for `g` continuous on `[μ, B]` and zero above `B`,
  `∫_{ℝ³} g(E(p)) d³p / ((2π)³ 2E(p)) = (1/(4π²)) ∫_μ^B √(E² − μ²) g(E) dE`, with
  `E(p) = √(‖p‖² + μ²)` (`PolarMeasure.integral_radial_three`, then the substitution `E = √(r² + μ²)`).
* `width_from_lebesgue`: so the massive width `MassiveDaughterSpectrum.width` is the Lebesgue
  integral over the daughter's momentum, with the Lorentz-invariant measure `d³p/((2π)³ 2E)`, of
  the flux-weighted pair part `ρ(E) = 1/(2m) · 64 G² ⟨pair⟩` (`pairPart`, equal to `ρ` by
  `pair_density`) cut at the endpoint. The electron measure is no longer supplied.

Still supplied in the width chain: the flux `1/(2m)` (the definition of a rate). The factorization
of the three-body measure into daughter measure × pair two-body average is derived
(`PairShell.shell_integral`, `PairSphere.shell_tensor_normalized`).
-/

noncomputable section
open MeasureTheory Set
namespace PMElementaryParticles.ElectronMeasure
open MassiveVolume

lemma E_hasDerivAt' {μ : ℝ} (hμ : μ ≠ 0) (r : ℝ) : HasDerivAt (E μ) (r / E μ r) r := by
  have h1 : HasDerivAt (fun r : ℝ => r ^ 2 + μ ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).add_const (μ ^ 2)
  have h2 := h1.sqrt (by positivity)
  unfold E
  exact h2.congr_deriv (by rw [mul_div_mul_left _ _ (two_ne_zero)])

lemma E_pos' {μ : ℝ} (hμ : μ ≠ 0) (r : ℝ) : 0 < E μ r := Real.sqrt_pos.mpr (by positivity)

lemma E_continuous (μ : ℝ) : Continuous (E μ) := by unfold E; fun_prop

lemma sqrt_shell {μ r : ℝ} (hr : 0 ≤ r) : Real.sqrt (E μ r ^ 2 - μ ^ 2) = r := by
  unfold E
  rw [Real.sq_sqrt (by positivity), add_sub_cancel_right, Real.sqrt_sq hr]

/-- **The massive Lorentz-invariant measure, radially reduced to the energy.** -/
theorem massive_lorentz_measure {μ B : ℝ} (hμ : 0 < μ) (hB : μ ≤ B) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc μ B)) (hz : ∀ e, B < e → g e = 0) :
    ∫ x : EuclideanSpace ℝ (Fin 3), g (E μ ‖x‖) / ((2 * Real.pi) ^ 3 * (2 * E μ ‖x‖)) =
      (1 / (4 * Real.pi ^ 2)) * ∫ e in μ..B, Real.sqrt (e ^ 2 - μ ^ 2) * g e := by
  have hμ0 : μ ≠ 0 := hμ.ne'
  set R := Real.sqrt (B ^ 2 - μ ^ 2) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hER : E μ R = B := by
    unfold E; rw [hR, Real.sq_sqrt (by nlinarith), sub_add_cancel, Real.sqrt_sq (by linarith)]
  have hE0 : E μ 0 = μ := by unfold E; simp [Real.sqrt_sq hμ.le]
  rw [PolarMeasure.integral_radial_three
    (fun r => g (E μ r) / ((2 * Real.pi) ^ 3 * (2 * E μ r)))]
  -- cut at `R`
  have hcut : ∫ r in Ioi (0 : ℝ), r ^ 2 * (g (E μ r) / ((2 * Real.pi) ^ 3 * (2 * E μ r))) =
      ∫ r in Ioc 0 R, r ^ 2 * (g (E μ r) / ((2 * Real.pi) ^ 3 * (2 * E μ r))) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Ioc_subset_Ioi_self ?_
    rintro x ⟨hx0, hxR⟩
    simp only [mem_Ioc, not_and, not_le] at hxR
    have hx : R < x := hxR hx0
    have : B < E μ x := by
      unfold E
      rw [show B = Real.sqrt (B ^ 2) from (Real.sqrt_sq (by linarith)).symm]
      apply Real.sqrt_lt_sqrt (by positivity)
      have h1 : R ^ 2 = B ^ 2 - μ ^ 2 := Real.sq_sqrt (by nlinarith)
      nlinarith
    rw [hz _ this]; simp
  rw [hcut, ← intervalIntegral.integral_of_le hR0]
  -- substitute `e = E(r)`
  set G : ℝ → ℝ := fun e => (1 / ((2 * Real.pi) ^ 3 * 2)) * (Real.sqrt (e ^ 2 - μ ^ 2) * g e)
  have hpt : ∀ r ∈ uIcc 0 R, r ^ 2 * (g (E μ r) / ((2 * Real.pi) ^ 3 * (2 * E μ r))) =
      (G ∘ E μ) r * (r / E μ r) := by
    intro r hr
    rw [uIcc_of_le hR0] at hr
    have hE := E_pos' hμ0 r
    simp only [G, Function.comp, sqrt_shell hr.1]
    field_simp
  rw [intervalIntegral.integral_congr hpt]
  have hcont' : ContinuousOn (fun r => r / E μ r) (uIcc 0 R) :=
    (continuous_id.div (E_continuous μ) (fun r => (E_pos' hμ0 r).ne')).continuousOn
  have himg : E μ '' uIcc 0 R ⊆ Icc μ B := by
    rintro _ ⟨r, hr, rfl⟩
    rw [uIcc_of_le hR0] at hr
    have h1 : R ^ 2 = B ^ 2 - μ ^ 2 := Real.sq_sqrt (by nlinarith)
    constructor
    · calc μ = Real.sqrt (μ ^ 2) := (Real.sqrt_sq hμ.le).symm
        _ ≤ E μ r := Real.sqrt_le_sqrt (by nlinarith)
    · calc E μ r ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hr.1, hr.2])
        _ = B := Real.sqrt_sq (by linarith)
  have hGc : ContinuousOn G (E μ '' uIcc 0 R) := by
    refine ContinuousOn.mono ?_ himg
    exact continuousOn_const.mul ((Continuous.continuousOn (by fun_prop)).mul hg)
  rw [intervalIntegral.integral_comp_mul_deriv' (fun r _ => E_hasDerivAt' hμ0 r) hcont' hGc,
    hE0, hER]
  simp only [G]
  rw [intervalIntegral.integral_const_mul]
  have hpi := Real.pi_pos
  field_simp
  ring

/-- The flux-weighted pair part of the density: `rate = (P/(4π²)) · pairPart`. -/
def pairPart (G m μ e : ℝ) : ℝ :=
  G ^ 2 * (e * (3 * m ^ 2 + 3 * μ ^ 2 - 4 * m * e) - 2 * m * μ ^ 2) / (3 * Real.pi)

theorem rate_eq_measure_mul (G m μ e : ℝ) :
    MassiveDaughterSpectrum.rate G m μ e =
      Real.sqrt (e ^ 2 - μ ^ 2) / (4 * Real.pi ^ 2) * pairPart G m μ e := by
  unfold MassiveDaughterSpectrum.rate MassiveDaughterSpectrum.momentum pairPart
  have hpi := Real.pi_pos
  field_simp
  ring

/-- **The massive width as a Lebesgue integral over the daughter's momentum.** -/
theorem width_from_lebesgue (G m μ : ℝ) (hμ : 0 < μ) (hm : μ < m) :
    MassiveDaughterSpectrum.width G m μ =
      ∫ x : EuclideanSpace ℝ (Fin 3),
        (if E μ ‖x‖ ≤ MassiveDaughterSpectrum.endpoint m μ then pairPart G m μ (E μ ‖x‖) else 0) /
          ((2 * Real.pi) ^ 3 * (2 * E μ ‖x‖)) := by
  have hB := (MassiveDaughterSpectrum.threshold m μ (hμ.trans hm) hμ.le hm).1.le
  have hc : ContinuousOn (fun e => if e ≤ MassiveDaughterSpectrum.endpoint m μ then
      pairPart G m μ e else 0) (Icc μ (MassiveDaughterSpectrum.endpoint m μ)) := by
    refine ContinuousOn.congr (f := pairPart G m μ) (by unfold pairPart; fun_prop) ?_
    intro e he; simp [he.2]
  have h := massive_lorentz_measure hμ hB _ hc (fun e he => by simp [not_le.mpr he])
  rw [h]
  unfold MassiveDaughterSpectrum.width
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun e he => ?_)
  rw [uIcc_of_le hB] at he
  simp only [he.2, ↓reduceIte, rate_eq_measure_mul]
  ring

end PMElementaryParticles.ElectronMeasure
