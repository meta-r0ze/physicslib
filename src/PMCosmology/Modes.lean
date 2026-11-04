import PMCosmology.Primordial
import PMAction.RealSpaceFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Modes: the substrate's Fourier block, and a generic free-mode lemma

**The substrate mode structure is not chosen here.** Paper II's real-space split update
has discrete Fourier blocks: `PMAction.RealSpaceFourier.hat_update` proves each Fourier
coefficient evolves by its momentum-space block, and `eigen_iff` identifies the torus
spectrum with the union of those block spectra. That is what the E8 update actually has,
and `substrate_mode_evolves` below re-exports it.

The generic `mode k A φ t = A cos(kt+φ)` is **only a test function** for the linear ODE
`h'' + k²h = 0`; it is *not* the substrate mode. It is used solely to state the negative
structural fact that a source-free linear equation does not fix the amplitude/power. The
physical spectrum needs the substrate blocks (`hat_update`) plus initial data or a source;
this module makes no spectrum claim.
-/

noncomputable section
namespace PMCosmology.Modes
open Real
open Matrix PMAction PMAction.RealSpaceFourier

/-- **The substrate's actual mode evolution** (re-export): a Fourier coefficient of the
real-space split update at lattice momentum `m` evolves by its momentum block. This is
the E8-grounded mode evolution, not a chosen ODE. -/
theorem substrate_mode_evolves (n : ℕ) (τ : ℝ)
    (ψ : Lat n × PMAction.ConcreteFermion.Sites → ℂ) (m : Lat n) :
    hat n (VacuumSplit.update (n + 1) τ *ᵥ ψ) m =
      VacuumSplit.momentumUpdate (kvec n (cvec n m)) τ *ᵥ hat n ψ m :=
  hat_update n τ ψ m

/-- A **generic** Fourier test function `A cos(k t + φ)` (not the substrate mode). -/
def mode (k A φ : ℝ) : ℝ → ℝ := fun t => A * Real.cos (k * t + φ)

/-- First derivative of the generic test mode. -/
theorem mode_hasDerivAt (k A φ t : ℝ) :
    HasDerivAt (fun y : ℝ => A * Real.cos (k * y + φ))
      (-(A * k) * Real.sin (k * t + φ)) t := by
  have hlin : HasDerivAt (fun x : ℝ => k * x + φ) k t := by
    simpa using ((hasDerivAt_id t).const_mul k).const_add φ
  have hcos : HasDerivAt (fun x : ℝ => Real.cos x) (-Real.sin (k * t + φ)) (k * t + φ) :=
    Real.hasDerivAt_cos (k * t + φ)
  have h2 := hcos.comp t hlin
  have h3 := h2.const_mul A
  convert h3 using 1
  · funext y; simp [Function.comp]
  · ring

/-- Second derivative of the generic test mode. -/
theorem mode_second_deriv (k A φ t : ℝ) :
    HasDerivAt (fun x : ℝ => -(A * k) * Real.sin (k * x + φ))
      (-(A * k ^ 2) * Real.cos (k * t + φ)) t := by
  have hlin : HasDerivAt (fun x : ℝ => k * x + φ) k t := by
    simpa using ((hasDerivAt_id t).const_mul k).const_add φ
  have hsin : HasDerivAt (fun x : ℝ => Real.sin x) (Real.cos (k * t + φ)) (k * t + φ) :=
    Real.hasDerivAt_sin (k * t + φ)
  have h2 := hsin.comp t hlin
  have h3 := h2.const_mul (-(A * k))
  convert h3 using 1
  · funext y; simp [Function.comp]
  · ring

/-- The generic test mode satisfies `h'' + k²h = 0` at the derivative-value level. -/
theorem mode_ode (k A φ t : ℝ) :
    (-(A * k ^ 2) * Real.cos (k * t + φ)) + k ^ 2 * mode k A φ t = 0 := by
  simp only [mode]
  ring

/-- **Generic negative result:** any amplitude is the value at `t = 0` (with `φ = 0`),
so the source-free ODE does not select the amplitude. -/
theorem amplitude_free (k A : ℝ) : mode k A 0 0 = A := by
  simp [mode]

/-- Every nonnegative power is realized by a generic source-free test mode, so the ODE
alone does not select the power spectrum. -/
theorem power_free (k P : ℝ) (hP : 0 ≤ P) :
    mode k (Real.sqrt P) 0 0 = Real.sqrt P ∧ (mode k (Real.sqrt P) 0 0) ^ 2 = P := by
  refine ⟨by simp [mode], ?_⟩
  rw [amplitude_free, Real.sq_sqrt hP]

/-- At `k = 0` the generic test mode is a free constant. -/
theorem homogeneous_free (A t : ℝ) : mode 0 A 0 t = A := by
  simp [mode]

end PMCosmology.Modes
