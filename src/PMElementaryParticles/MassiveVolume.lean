import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The massive two-body volume: `Φ₂(m₁, m₂) = (2P/Q) · Φ₂(0, 0)`

`PolarMeasure.two_body_from_lebesgue`: the massless two-body factor `Φ₂ = 1/(8π)` is the
energy-shell derivative of the cumulative pair integral, whose radial form is `∫₀^{M/2} 1/(4π) dr`.
With masses `m₁`, `m₂` the back-to-back pair at momentum `r` has energies `Eᵢ(r) = √(r² + mᵢ²)`,
total energy `Q(r) = E₁ + E₂`, and Lorentz weights `1/(2E₁)(2E₂)`; the same `ℝ³` reduction gives the
cumulative `(1/(4π)) ∫₀^P r²/(E₁E₂) dr` up to the shell at momentum `P`.

* `cumulative_deriv`: the cumulative's `P`-derivative is `P²/(E₁E₂)/(4π)`.
* `energy_deriv`: `dQ/dP = P/E₁ + P/E₂ = P Q/(E₁E₂)`.
* `shell_density_at_energy` proves the actual energy derivative above threshold
  for nonnegative masses. `shell_density`: if the cumulative, read as a function `G` of the total energy, has derivative `g`
  at `Q(P)`, then `g = (1/(8π)) · (2P/Q)`. So the massive two-body volume is `2P/Q` times the
  massless one (`massless_case`: `m₁ = m₂ = 0` gives `2P/Q = 1`).
-/

noncomputable section
namespace PMElementaryParticles.MassiveVolume

/-- Energy of a leg of mass `m` at momentum `r`. -/
def E (m r : ℝ) : ℝ := Real.sqrt (r ^ 2 + m ^ 2)

/-- Total pair energy at momentum `r`. -/
def Q (m₁ m₂ r : ℝ) : ℝ := E m₁ r + E m₂ r

/-- The cumulative two-body integral up to the shell at momentum `P`. -/
def cumulative (m₁ m₂ P : ℝ) : ℝ :=
  (1 / (4 * Real.pi)) * ∫ r in (0 : ℝ)..P, r ^ 2 / (E m₁ r * E m₂ r)

lemma E_pos (m : ℝ) {r : ℝ} (hr : r ≠ 0) : 0 < E m r :=
  Real.sqrt_pos.mpr (by positivity)

lemma E_hasDerivAt (m : ℝ) {r : ℝ} (hr : r ≠ 0) : HasDerivAt (E m) (r / E m r) r := by
  have h1 : HasDerivAt (fun r : ℝ => r ^ 2 + m ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).add_const (m ^ 2)
  have h2 := h1.sqrt (by positivity)
  unfold E
  exact h2.congr_deriv (by rw [mul_div_mul_left _ _ (two_ne_zero)])

lemma integrand_continuousAt (m₁ m₂ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ContinuousAt (fun r => r ^ 2 / (E m₁ r * E m₂ r)) r := by
  apply ContinuousAt.div (by fun_prop)
  · exact ((E_hasDerivAt m₁ hr).continuousAt).mul (E_hasDerivAt m₂ hr).continuousAt
  · exact (mul_pos (E_pos m₁ hr) (E_pos m₂ hr)).ne'

lemma integrand_continuous (m₁ m₂ : ℝ) (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) :
    Continuous (fun r : ℝ => r ^ 2 / (E m₁ r * E m₂ r)) := by
  have hE : ∀ m : ℝ, m ≠ 0 → ∀ r : ℝ, 0 < r ^ 2 + m ^ 2 := fun m hm r => by positivity
  apply Continuous.div (by fun_prop)
  · unfold E; fun_prop
  · intro r
    exact (mul_pos (Real.sqrt_pos.mpr (hE m₁ h₁ r)) (Real.sqrt_pos.mpr (hE m₂ h₂ r))).ne'

theorem energy_deriv (m₁ m₂ : ℝ) {P : ℝ} (hP : P ≠ 0) :
    HasDerivAt (Q m₁ m₂) (P * Q m₁ m₂ P / (E m₁ P * E m₂ P)) P := by
  have h := (E_hasDerivAt m₁ hP).add (E_hasDerivAt m₂ hP)
  have h1 := (E_pos m₁ hP).ne'; have h2 := (E_pos m₂ hP).ne'
  show HasDerivAt (E m₁ + E m₂) _ P
  refine h.congr_deriv ?_
  unfold Q; rw [div_add_div _ _ h1 h2]; ring

/-- The cumulative's `P`-derivative, for massive legs (the integrand is then continuous on `ℝ`). -/
theorem cumulative_deriv (m₁ m₂ : ℝ) (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) (P : ℝ) :
    HasDerivAt (cumulative m₁ m₂)
      ((1 / (4 * Real.pi)) * (P ^ 2 / (E m₁ P * E m₂ P))) P := by
  have hc := integrand_continuous m₁ m₂ h₁ h₂
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 P)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  exact h.const_mul _

/-- **The massive shell density.** If the cumulative, as a function `G` of the pair energy, is
differentiable at `Q(P)`, its derivative is `(1/(8π))·(2P/Q)`. -/
theorem shell_density (m₁ m₂ : ℝ) (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) {P : ℝ} (hP : 0 < P)
    (G : ℝ → ℝ) (g : ℝ) (hG : HasDerivAt G g (Q m₁ m₂ P))
    (hGQ : ∀ p, G (Q m₁ m₂ p) = cumulative m₁ m₂ p) :
    g = (1 / (8 * Real.pi)) * (2 * P / Q m₁ m₂ P) := by
  have hP0 : P ≠ 0 := hP.ne'
  have hcomp := hG.comp P (energy_deriv m₁ m₂ hP0)
  have hF : HasDerivAt (fun p => G (Q m₁ m₂ p))
      ((1 / (4 * Real.pi)) * (P ^ 2 / (E m₁ P * E m₂ P))) P := by
    have : (fun p => G (Q m₁ m₂ p)) = cumulative m₁ m₂ := funext hGQ
    rw [this]; exact cumulative_deriv m₁ m₂ h₁ h₂ P
  have huniq := hcomp.unique hF
  have hE1 := E_pos m₁ hP0; have hE2 := E_pos m₂ hP0
  have hQ : 0 < Q m₁ m₂ P := add_pos hE1 hE2
  have hpi := Real.pi_pos
  have : g = (1 / (4 * Real.pi)) * (P ^ 2 / (E m₁ P * E m₂ P)) /
      (P * Q m₁ m₂ P / (E m₁ P * E m₂ P)) := by
    rw [← huniq]; field_simp
  rw [this]; field_simp; ring

/-- The pair has positive rest momentum exactly above the two-mass threshold. -/
theorem exists_pos_momentum_iff (m₁ m₂ q : ℝ) (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) :
    (∃ P : ℝ, 0 < P ∧ Q m₁ m₂ P = q) ↔ m₁ + m₂ < q := by
  have hzero : Q m₁ m₂ 0 = m₁ + m₂ := by
    simp [Q, E, Real.sqrt_sq h₁, Real.sqrt_sq h₂]
  constructor
  · rintro ⟨P, hP, rfl⟩
    have hlt (m : ℝ) : E m 0 < E m P := by
      unfold E
      apply Real.sqrt_lt_sqrt (by positivity)
      nlinarith [sq_pos_of_pos hP]
    rw [← hzero]
    exact add_lt_add (hlt m₁) (hlt m₂)
  · intro hq
    have hq0 : 0 < q := lt_of_le_of_lt (add_nonneg h₁ h₂) hq
    have hE (m : ℝ) : q ≤ E m q := by
      calc
        q = Real.sqrt (q ^ 2) := (Real.sqrt_sq hq0.le).symm
        _ ≤ E m q := Real.sqrt_le_sqrt (by linarith [sq_nonneg m])
    have htop : q ≤ Q m₁ m₂ q :=
      le_trans (hE m₁) (le_add_of_nonneg_right (Real.sqrt_nonneg _))
    have hcont : Continuous (Q m₁ m₂) := by unfold Q E; fun_prop
    obtain ⟨P, hP, he⟩ := intermediate_value_Icc hq0.le hcont.continuousOn
      (show q ∈ Set.Icc (Q m₁ m₂ 0) (Q m₁ m₂ q) from ⟨by rw [hzero]; exact hq.le, htop⟩)
    refine ⟨P, lt_of_le_of_ne hP.1 ?_, he⟩
    rintro rfl
    rw [hzero] at he
    exact hq.ne he

/-- Pair rest momentum expressed in terms of the total pair energy. -/
def momentumAt (m₁ m₂ q : ℝ) : ℝ :=
  Real.sqrt (((q ^ 2 + m₁ ^ 2 - m₂ ^ 2) / (2 * q)) ^ 2 - m₁ ^ 2)

theorem momentumAt_Q (m₁ m₂ P : ℝ) (hP : 0 < P) :
    momentumAt m₁ m₂ (Q m₁ m₂ P) = P := by
  have hE (m : ℝ) : E m P ^ 2 = P ^ 2 + m ^ 2 := Real.sq_sqrt (by positivity)
  have hQ : 0 < Q m₁ m₂ P := add_pos (E_pos _ hP.ne') (E_pos _ hP.ne')
  have he : ((Q m₁ m₂ P) ^ 2 + m₁ ^ 2 - m₂ ^ 2) / (2 * Q m₁ m₂ P) = E m₁ P := by
    apply (div_eq_iff (by positivity : 2 * Q m₁ m₂ P ≠ 0)).mpr
    unfold Q
    nlinarith [hE m₁, hE m₂]
  rw [momentumAt, he, hE, add_sub_cancel_right, Real.sqrt_sq hP.le]

private theorem cumulative_deriv_left_zero (m : ℝ) (hm : m ≠ 0) (P : ℝ) :
    HasDerivAt (cumulative 0 m)
      ((1 / (4 * Real.pi)) * (P ^ 2 / (E 0 P * E m P))) P := by
  have he (r : ℝ) : r ^ 2 / (E 0 r * E m r) = |r| / E m r := by
    have hE : E 0 r = |r| := by simp [E, Real.sqrt_sq_eq_abs]
    rw [hE]
    by_cases hr : r = 0
    · simp [hr]
    · have hm' := E_pos m hr
      field_simp [abs_ne_zero.mpr hr, hm'.ne']
      nlinarith [sq_abs r]
  have hcont : Continuous (fun r => |r| / E m r) := by
    apply continuous_abs.div (by unfold E; fun_prop)
    intro r
    exact (Real.sqrt_pos.mpr (by positivity : 0 < r ^ 2 + m ^ 2)).ne'
  unfold cumulative
  simp_rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 P)
    (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt).const_mul _

/-- Above zero rest momentum, the radial derivative also exists for massless
and mixed-mass pairs. At two zero masses the integrand is one almost everywhere. -/
theorem cumulative_deriv_of_pos (m₁ m₂ : ℝ) {P : ℝ} (hP : 0 < P) :
    HasDerivAt (cumulative m₁ m₂)
      ((1 / (4 * Real.pi)) * (P ^ 2 / (E m₁ P * E m₂ P))) P := by
  by_cases h₁ : m₁ = 0
  · subst m₁
    by_cases h₂ : m₂ = 0
    · subst m₂
      have he (r : ℝ) (hr : r ≠ 0) : r ^ 2 / (E 0 r * E 0 r) = 1 := by
        have hE : E 0 r = |r| := by simp [E, Real.sqrt_sq_eq_abs]
        rw [hE, ← sq, sq_abs]
        exact div_self (pow_ne_zero _ hr)
      have hc : cumulative 0 0 = fun r => (1 / (4 * Real.pi)) * r := by
        funext r
        unfold cumulative
        congr 1
        calc
          (∫ x in (0 : ℝ)..r, x ^ 2 / (E 0 x * E 0 x)) =
              ∫ _ in (0 : ℝ)..r, (1 : ℝ) := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with x hx _
            exact he x hx
          _ = r := by simp
      rw [hc, he P hP.ne', mul_one]
      simpa using (hasDerivAt_id P).const_mul (1 / (4 * Real.pi))
    · exact cumulative_deriv_left_zero _ h₂ _
  · by_cases h₂ : m₂ = 0
    · subst m₂
      have hcomm : cumulative m₁ 0 = cumulative 0 m₁ := by
        funext r
        simp [cumulative, mul_comm (E m₁ _) (E 0 _)]
      rw [hcomm, mul_comm (E m₁ P) (E 0 P)]
      exact cumulative_deriv_left_zero _ h₁ _
    · exact cumulative_deriv _ _ h₁ h₂ P

/-- The massive shell density is the derivative of the explicitly
energy-parameterized radial cumulative above threshold. -/
theorem shell_density_at_energy (m₁ m₂ q : ℝ) (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂)
    (hq : m₁ + m₂ < q) :
    HasDerivAt (fun s => cumulative m₁ m₂ (momentumAt m₁ m₂ s))
      ((1 / (8 * Real.pi)) * (2 * momentumAt m₁ m₂ q / q)) q := by
  obtain ⟨P, hP, he⟩ := (exists_pos_momentum_iff m₁ m₂ q h₁ h₂).mpr hq
  have hinv : momentumAt m₁ m₂ q = P := by rw [← he, momentumAt_Q _ _ _ hP]
  have hq0 : 0 < q := lt_of_le_of_lt (add_nonneg h₁ h₂) hq
  have hcont : ContinuousAt (momentumAt m₁ m₂) q := by
    unfold momentumAt
    fun_prop (disch := positivity)
  have hder : HasDerivAt (Q m₁ m₂)
      (P * q / (E m₁ P * E m₂ P)) (momentumAt m₁ m₂ q) := by
    rw [hinv, ← he]
    exact energy_deriv _ _ hP.ne'
  have hlocal : ∀ᶠ s in nhds q, Q m₁ m₂ (momentumAt m₁ m₂ s) = s := by
    filter_upwards [lt_mem_nhds hq] with s hs
    obtain ⟨r, hr, h⟩ := (exists_pos_momentum_iff m₁ m₂ s h₁ h₂).mpr hs
    rw [← h, momentumAt_Q _ _ _ hr]
  have hd := HasDerivAt.of_local_left_inverse hcont hder
    (by have := E_pos m₁ hP.ne'; have := E_pos m₂ hP.ne'; positivity) hlocal
  have hc := cumulative_deriv_of_pos m₁ m₂ hP
  rw [← hinv] at hc
  change HasDerivAt (cumulative m₁ m₂ ∘ momentumAt m₁ m₂) _ q
  convert hc.comp q hd using 1
  rw [hinv]
  field_simp [hP.ne', hq0.ne', (E_pos m₁ hP.ne').ne', (E_pos m₂ hP.ne').ne', Real.pi_ne_zero]
  ring

/-- Massless legs: `Q = 2P`, so `2P/Q = 1` and the factor is the massless `1/(8π)`. -/
theorem massless_case {P : ℝ} (hP : 0 < P) : 2 * P / Q 0 0 P = 1 := by
  have : Q 0 0 P = 2 * P := by
    unfold Q E; simp [Real.sqrt_sq hP.le]; ring
  rw [this]; field_simp

end PMElementaryParticles.MassiveVolume
