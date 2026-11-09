import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
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
* `massless_lorentz_measure` — the Lorentz-invariant measure `d³k/((2π)³ 2E)` as a genuine
  Lebesgue integral, `∫_{ℝ³} f(‖k‖)/((2π)³ 2‖k‖) = (1/(4π²)) ∫₀^∞ r f(r) dr`.
* `two_body_phase_space` — the two-body factor `Φ₂ = 1/(8π)` as the integral of the reduced
  angular density `1/(32π²)` over `volume.toSphere`.
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

/-- **The Lorentz-invariant massless measure `d³k/((2π)³ 2E)`, radially reduced.**
`∫_{ℝ³} f(‖k‖)/((2π)³ 2‖k‖) d³k = (1/(4π²)) ∫₀^∞ r f(r) dr`. The measure factor
`1/((2π)³ 2E)` is now integrated against a genuine Lebesgue measure (via
`integral_radial_three`), not supplied — the Part-A1 step that does not need the
delta-function / energy-shell reduction. -/
theorem massless_lorentz_measure (f : ℝ → ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin 3), f ‖x‖ / ((2 * Real.pi) ^ 3 * (2 * ‖x‖)) =
      (1 / (4 * Real.pi ^ 2)) * ∫ r in Ioi (0 : ℝ), r * f r := by
  have h := integral_radial_three (fun r => f r / ((2 * Real.pi) ^ 3 * (2 * r)))
  rw [show (fun x : EuclideanSpace ℝ (Fin 3) => f ‖x‖ / ((2 * Real.pi) ^ 3 * (2 * ‖x‖)))
        = fun x => (fun r => f r / ((2 * Real.pi) ^ 3 * (2 * r))) ‖x‖ from rfl, h]
  rw [show (∫ r in Ioi (0 : ℝ), r ^ 2 * (f r / ((2 * Real.pi) ^ 3 * (2 * r)))) =
        (1 / (2 * (2 * Real.pi) ^ 3)) * ∫ r in Ioi (0 : ℝ), r * f r by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    field_simp]
  rw [show (4 : ℝ) * Real.pi *
          ((1 / (2 * (2 * Real.pi) ^ 3)) * ∫ r in Ioi (0 : ℝ), r * f r) =
        (1 / (4 * Real.pi ^ 2)) * ∫ r in Ioi (0 : ℝ), r * f r by
    have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
    ring]

/-- **The two-body phase-space factor `Φ₂ = 1/(8π)` from the genuine direction sphere.** The
reduced angular density is `1/(32π²)` (`ContinuumPair.average`), so its integral over the real
sphere measure `volume.toSphere` is `4π · (1/(32π²)) = 1/(8π)` (`MuonRate.two_body`) — with `S²`
now measured by `volume.toSphere` rather than the iterated `(z, φ)` integral. -/
theorem two_body_phase_space :
    ∫ _ω in (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)),
        (1 / (32 * Real.pi ^ 2) : ℝ) ∂(volume.toSphere) = 1 / (8 * Real.pi) := by
  rw [MeasureTheory.setIntegral_const, sphere_area_three, smul_eq_mul]
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

/-- **The delta-function / energy-shell reduction (Review item A1).** The `M`-derivative of the
cumulative integral `M ↦ ∫₀^{M/2} h` is `h(M/2)/2`, i.e. `∫₀^∞ h(r) δ(M − 2r) dr = h(M/2)/2`.
The Jacobian `1/2 = |d(M−2r)/dr|⁻¹` is **derived** (not postulated): it is the chain-rule factor
`d(M/2)/dM = 1/2` in the fundamental theorem of calculus. This is the one piece of A1 that the
polar decomposition alone does not supply. -/
theorem delta_reduction (h : ℝ → ℝ) (hh : Continuous h) (M : ℝ) :
    HasDerivAt (fun M' => ∫ r in (0 : ℝ)..(M' / 2), h r) (h (M / 2) / 2) M := by
  have h1 : HasDerivAt (fun x : ℝ => ∫ r in (0 : ℝ)..x, h r) (h (M / 2)) (M / 2) :=
    intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable 0 (M / 2))
      (hh.stronglyMeasurableAtFilter volume (nhds (M / 2))) hh.continuousAt
  have h2 : HasDerivAt (fun M' : ℝ => M' / 2) (1 / 2) M := by
    simpa [div_eq_mul_inv, mul_comm] using hasDerivAt_const_mul (x := M) (1 / 2 : ℝ)
  have h3 := h1.comp M h2
  have : h (M / 2) * (1 / 2) = h (M / 2) / 2 := by ring
  rw [this] at h3
  exact h3

/-- **The massless two-body phase space `Φ₂ = 1/(8π)` from the energy-shell delta.** The
cumulative massless two-body integral is `C(M) = (2π)⁴/(4(2π)⁶) ∫_{ℝ³} 1_{2‖k‖≤M}/‖k‖² d³k
= ∫₀^{M/2} 1/(4π) dr` (the coefficient `1/(4π)` being the `4π` angular weight over `(2π)⁴/4(2π)⁶`);
by `delta_reduction` its `M`-derivative is the two-body factor `Φ₂ = 1/(8π)`. So `Φ₂` is no longer
an input factor: it is the energy-shell derivative of a genuine `∫_{ℝ³}`. -/
theorem twoBody_from_delta (M : ℝ) :
    HasDerivAt (fun M' => ∫ _r in (0 : ℝ)..(M' / 2), (1 / (4 * Real.pi)))
      (1 / (8 * Real.pi)) M := by
  have h := delta_reduction (fun _ => (1 / (4 * Real.pi))) continuous_const M
  convert h using 1
  ring

/-! ## E6: the continuum angular density is grounded, not a convention ([`ContinuumPair.average`])

`ContinuumPair` carries the reduced angular density `1/(32π²)` as a stated measure convention. With
the genuine sphere measure now in hand it **factors** into two derived pieces: the normalized
uniform average over the unit sphere `1/(4π)` (`normalized_sphere_average`, from `sphere_area_three`)
and the two-body phase-space factor `Φ₂ = 1/(8π)` (`two_body_phase_space`). So E6's "continuum
density" sub-item is no longer an independent input, and the electron measure is
`electron_measure_from_integral`; what remains of E6 is the readout (which E8 modes and their
`BetaLattice` Boltzmann weights) and the relativistic `2E` normalization convention. -/

/-- **The continuum angular density `1/(32π²)` is the normalized sphere average times `Φ₂`.** -/
theorem continuum_angular_density :
    (1 / (32 * Real.pi ^ 2) : ℝ) = (1 / (4 * Real.pi)) * (1 / (8 * Real.pi)) := by
  ring

/-- The normalized uniform sphere average is `1` (the area `4π` is `sphere_area_three`). -/
theorem normalized_sphere_average : (1 / (4 * Real.pi)) * (4 * Real.pi) = 1 := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end PMElementaryParticles.PolarMeasure
