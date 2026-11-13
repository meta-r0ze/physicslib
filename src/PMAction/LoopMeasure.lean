import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The one-loop log coefficient from the 4D measure

`ContactRunning` writes the contact's running in units of `(α/4π)·ln(M²/μ²)`. That unit is the
4D phase-space measure between two scales. A loop with a `1/k⁴` integrand, integrated over the
shell `μ < |k| < M` of 4D (Euclidean) momentum space with the measure `d⁴k/(2π)⁴`, gives
`|S³|/(2π)⁴ · ln(M/μ)`. With `|S³| = 2π²` this is `ln(M/μ)/(8π²)`, and with the coupling
`e² = 4πα` it is `(α/4π)·ln(M²/μ²)`.

* `volume_ball_fin_four`: the 4-ball has volume `(π²/2) r⁴` (Mathlib's Euclidean ball volume).
* `shell_density`: its radial derivative is `2π² r³`, the 3-sphere's area `|S³| r³`.
* `shell_integrand`: on the shell, `|S³| r³ / r⁴ = 2π² / r`.
* `log_shell`: `∫_μ^M 2π²/r dr = 2π² ln(M/μ)`.
* `phase_space_factor`: `2π²/(2π)⁴ = 1/(8π²)`.
* `log_unit`: `e²·ln(M/μ)/(8π²)` with `e² = 4πα` is `(α/4π)·ln(M²/μ²)`.

So the unit used in `ContactRunning` is the 4D measure's, not an extra input. It is the leading
log, set by the region between the two scales. On the substrate that region is far below the
lattice cutoff: `LeadingLog.leading_log` shows the D₄ shell of the link Laplacian's kernel gives
this unit up to `a²(M² − μ²)/(24π²)`. The per-diagram weights (the Ward identity's `W`, the `¼`
from `ContactRunning.loop_direction_average`, the `16`/`4` from `ContactFierz`) multiply it.
`self_energy_weight` below is the continuum form of `W = −1` (a Feynman-parameter average); the
substrate's is `LeadingLog.self_energy_weight`, where the `½` is the D₄ direction average.
-/

noncomputable section
namespace PMAction.LoopMeasure
open Real MeasureTheory Metric

/-- The 4-ball's volume. -/
theorem volume_ball_fin_four (x : EuclideanSpace ℝ (Fin 4)) (r : ℝ) :
    volume (ball x r) = ENNReal.ofReal r ^ 4 * ENNReal.ofReal (π ^ 2 / 2) := by
  norm_num [InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp) x]

/-- The 4-ball's volume as a real function of the radius. -/
def ballVolume (r : ℝ) : ℝ := π ^ 2 / 2 * r ^ 4

theorem volume_ball_eq (x : EuclideanSpace ℝ (Fin 4)) {r : ℝ} (hr : 0 ≤ r) :
    volume (ball x r) = ENNReal.ofReal (ballVolume r) := by
  rw [volume_ball_fin_four, ballVolume, ← ENNReal.ofReal_pow hr,
    ← ENNReal.ofReal_mul (pow_nonneg hr 4), mul_comm]

/-- **The shell density.** `d/dr (π²/2 · r⁴) = 2π² r³ = |S³| r³`. -/
theorem shell_density (r : ℝ) : HasDerivAt ballVolume (2 * π ^ 2 * r ^ 3) r := by
  have h := (hasDerivAt_pow 4 r).const_mul (π ^ 2 / 2)
  unfold ballVolume
  convert h using 1
  norm_num
  ring

/-- On the shell, the `1/k⁴` integrand times the shell density is `2π²/r`. -/
theorem shell_integrand {r : ℝ} (hr : r ≠ 0) : 2 * π ^ 2 * r ^ 3 / r ^ 4 = 2 * π ^ 2 * r⁻¹ := by
  field_simp

/-- **The log.** `∫_μ^M 2π²/r dr = 2π² ln(M/μ)`. -/
theorem log_shell {μ M : ℝ} (hμ : 0 < μ) (hM : 0 < M) :
    ∫ r in μ..M, 2 * π ^ 2 * r⁻¹ = 2 * π ^ 2 * Real.log (M / μ) := by
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hμ hM]

/-- **The phase-space factor.** `|S³|/(2π)⁴ = 2π²/(2π)⁴ = 1/(8π²)`. -/
theorem phase_space_factor : 2 * π ^ 2 / (2 * π) ^ 4 = 1 / (8 * π ^ 2) := by
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-- **The unit.** `e²·ln(M/μ)/(8π²)` with `e² = 4πα` equals `(α/4π)·ln(M²/μ²)`. -/
theorem log_unit (α μ M : ℝ) :
    4 * π * α * (1 / (8 * π ^ 2)) * Real.log (M / μ) =
      α / (4 * π) * Real.log (M ^ 2 / μ ^ 2) := by
  have hπ : π ≠ 0 := pi_ne_zero
  rw [show M ^ 2 / μ ^ 2 = (M / μ) ^ 2 by ring, Real.log_pow]
  field_simp
  ring

/-- The Feynman-parameter average `∫₀¹ x dx = 1/2`. -/
theorem feynman_weight : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
  rw [integral_id]
  norm_num

/-- **The self-energy weight.** In Feynman gauge the self-energy's log part is the vertex
contraction `γ^σ k̸ γ_σ = −2 k̸` (`ContactRunning.contraction`, linear in `k̸`) times the
Feynman-parameter weight `∫₀¹ (1 − x) dx = 1 − ∫₀¹ x dx = 1/2` of the external momentum, in units
of `log_unit`: `W = −2 · ½ = −1`. -/
theorem self_energy_weight : (-2 : ℝ) * (1 - ∫ x in (0 : ℝ)..1, x) = -1 := by
  rw [feynman_weight]
  norm_num

end PMAction.LoopMeasure
