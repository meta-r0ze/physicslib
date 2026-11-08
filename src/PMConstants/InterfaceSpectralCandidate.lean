import PMConstants.InterfaceCorrection
import PMAction.D4Gauge

/-! **Simplest isotropic root-sum response candidate.**

This is a candidate, not a derivation of the response law.  At zero momentum every
D₄ root has squared length two, so the isotropic root sum is `24/(q²+2)`.  Feeding
it into `K = 1 + α·Σ` gives a `Δr` that is far above the Z-anchor window.  The
candidate is therefore excluded; the point is to keep the substrate calculation
separate from the later comparison.
-/

noncomputable section
namespace PMConstants.InterfaceSpectralCandidate

open PMConstants PMAction.D4Gauge

/-- Isotropic root-sum response at momentum scale `q²`. -/
def rootSpectralResponse (q2 : ℝ) : ℝ :=
  ∑ _k ∈ roots, 1 / (q2 + 2)

theorem rootSpectralResponse_eq (q2 : ℝ) :
    rootSpectralResponse q2 = 24 / (q2 + 2) := by
  unfold rootSpectralResponse
  rw [Finset.sum_const, roots_card]
  norm_num
  ring

/-- Candidate interface factor `K = 1 + α·Σ`. -/
def Ksub (q2 : ℝ) : ℝ :=
  1 + PMConstants.CertifiedConstants.α * rootSpectralResponse q2

/-- Candidate on-shell correction. -/
def deltaRsub (q2 : ℝ) : ℝ :=
  1 - 1 / Ksub q2

theorem Ksub_zero : Ksub 0 = 1 + 12 * PMConstants.CertifiedConstants.α := by
  unfold Ksub
  rw [rootSpectralResponse_eq]
  norm_num
  ring

/-- The simplest isotropic root sum puts `Δr` above the Z-anchor window. -/
theorem simple_root_sum_excluded : (0.08 : ℝ) < deltaRsub 0 := by
  have ha := PMConstants.CertifiedConstants.alpha_bounds
  have hK : (1.087 : ℝ) < Ksub 0 := by
    rw [Ksub_zero]
    nlinarith [ha.1]
  have hKpos : (0 : ℝ) < Ksub 0 := by linarith
  have hK2 : (1 / 0.92 : ℝ) < Ksub 0 := by
    have hconst : (1 / 0.92 : ℝ) < 1.087 := by norm_num
    linarith
  have hinv : 1 / Ksub 0 < 0.92 := by
    rw [div_lt_iff₀ hKpos]
    nlinarith
  unfold deltaRsub
  linarith

end PMConstants.InterfaceSpectralCandidate
