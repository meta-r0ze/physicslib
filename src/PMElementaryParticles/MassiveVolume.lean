import Mathlib.Analysis.SpecialFunctions.Sqrt
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
* `shell_density`: if the cumulative, read as a function `G` of the total energy, has derivative `g`
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

/-- Massless legs: `Q = 2P`, so `2P/Q = 1` and the factor is the massless `1/(8π)`. -/
theorem massless_case {P : ℝ} (hP : 0 < P) : 2 * P / Q 0 0 P = 1 := by
  have : Q 0 0 P = 2 * P := by
    unfold Q E; simp [Real.sqrt_sq hP.le]; ring
  rw [this]; field_simp

end PMElementaryParticles.MassiveVolume
