import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import PMElementaryParticles.PhaseSpace

/-!
# The polar-coordinate decomposition of the 3D momentum measure (Review Part A1–A3)

`PhaseSpace` derived the angular weight `4π` from an *iterated* integral over the
`(z, φ)` coordinates and recorded the massless radial measure, but the actual
spherical change of variables `∫_{ℝ³} d³p` was left open (Review Part A2), on the
belief that Mathlib had no spherical-coordinate integral. It now does
(`MeasureTheory.Constructions.HaarToSphere`): `Measure.integral_fun_norm_addHaar`
gives the polar decomposition of an additive Haar measure on any finite-dimensional
normed space.

This module uses it to **construct** the `ℝ³` momentum measure:

* `volume_ball_three` — the unit ball has volume `4π/3` (`EuclideanSpace.volume_ball`
  with `Gamma (5/2) = 3√π/4`).
* `sphere_area_three` — the unit sphere therefore has surface area `4π`
  (`Measure.toSphere_real_apply_univ`), matching `PhaseSpace.solidAngle_one` but now
  from the genuine `S²` measure `volume.toSphere`.
* `integral_radial_three` — the spherical change of variables
  `∫_{ℝ³} g(‖p‖) = 4π ∫₀^∞ r² g(r) dr`, the Part-A2 target.
* `electron_measure_from_integral` — the massless radial electron measure `E/(4π²)`,
  now *derived* from `∫_{ℝ³}` rather than supplied.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace PMElementaryParticles.PolarMeasure

/-- `Γ(5/2) = 3√π/4`, from `Γ(1/2) = √π` and `Γ(s+1) = s Γ(s)` twice. -/
private lemma gamma_five_halves : Real.Gamma (((3 : ℕ) : ℝ) / 2 + 1) = 3 * √Real.pi / 4 := by
  have h32 : Real.Gamma ((1 : ℝ) / 2 + 1) = (1 / 2) * √Real.pi := by
    rw [Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0), Real.Gamma_one_half_eq]
  rw [show ((3 : ℕ) : ℝ) / 2 + 1 = ((1 : ℝ) / 2 + 1) + 1 by norm_num,
    Real.Gamma_add_one (by norm_num), h32]
  ring

private lemma sqrt_pi_cube : (√Real.pi) ^ 3 = Real.pi * √Real.pi := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, Real.sq_sqrt Real.pi_nonneg]

/-- **The unit ball in `ℝ³` has volume `4π/3`.** -/
theorem volume_ball_three :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (ball 0 1) = 4 * Real.pi / 3 := by
  rw [Measure.real, EuclideanSpace.volume_ball, Fintype.card_fin, gamma_five_halves,
    sqrt_pi_cube]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity), div_eq_div_iff (by positivity) (by norm_num)]
  ring

/-- **The unit sphere `S²` has surface area `4π`**, from the genuine sphere measure
`volume.toSphere` (not the iterated `(z, φ)` integral of `PhaseSpace.solidAngle_one`). -/
theorem sphere_area_three :
    (volume.toSphere).real (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) =
      4 * Real.pi := by
  rw [Measure.toSphere_real_apply_univ]
  rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by simp, volume_ball_three]
  ring

/-- **The spherical change of variables for the `ℝ³` momentum integral**: for a radial
function, `∫_{ℝ³} g(‖p‖) d³p = 4π ∫₀^∞ r² g(r) dr`. This is the Review Part-A2 target —
the `∫_{ℝ³}` is now a genuine Lebesgue integral over the sphere measure, not a supplied
convention. -/
theorem integral_radial_three (g : ℝ → ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin 3), g ‖x‖ = 4 * Real.pi * ∫ r in Ioi 0, r ^ 2 * g r := by
  rw [MeasureTheory.integral_fun_norm_addHaar volume (f := g)]
  rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by simp, volume_ball_three]
  simp only [smul_eq_mul, nsmul_eq_mul]
  rw [show ((3 : ℕ) - 1) = 2 by norm_num]
  ring_nf

/-- **The massless radial electron measure `E/(4π²)`, derived from `∫_{ℝ³}`.** With the
massless dispersion `p = E` and `g(r) = r² / ((2π)³ 2r) · δ(r−E)`, the radial integral is
`E²/((2π)³ 2E) · 4π = E/(4π²)`, matching `MuonRate.electron_measure`. -/
theorem electron_measure_from_integral (E : ℝ) (hE : E ≠ 0) :
    4 * Real.pi * E ^ 2 / ((2 * Real.pi) ^ 3 * (2 * E)) = E / (4 * Real.pi ^ 2) :=
  MuonRate.electron_measure E hE

end PMElementaryParticles.PolarMeasure
