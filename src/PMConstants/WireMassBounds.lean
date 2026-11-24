import PMAction.WireResonanceSpectrum
import PMConstants.CertifiedConstants

/-!
# A geometric bound for the bare wire benchmark

If the normalized restoring coefficient is taken to be the conserving
two-leg admittance `α/2`, the normalized bare wire has a small middle-to-heavy
mass ratio. The condition identifies a rate with an admittance. The bound
uses that benchmark value and the geometric enclosure of `α`.
-/

noncomputable section
namespace PMConstants.WireMassBounds

open CertifiedConstants

/-- Exact interval for the bare middle-to-heavy ratio evaluated at
`k = α/2`. The mass formula is from `WireResonanceSpectrum.bare_mass_spectrum`. -/
theorem bare_middle_heavy_bounds :
    let k := α / 2
    let ratio := Real.sqrt (3 * k ^ 2) / Real.sqrt (2 + k ^ 2)
    0.0044 < ratio ∧ ratio < 0.0045 := by
  intro k ratio
  have hklo : 0.00364 < k := by dsimp [k]; linarith [alpha_bounds.1]
  have hkhi : k < 0.00365 := by dsimp [k]; linarith [alpha_bounds.2]
  have hkloSq : (0.00364 : ℝ) ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ (by norm_num) hklo.le 2
  have hkhiSq : k ^ 2 ≤ (0.00365 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hkhi.le 2
  have hnum := Real.sq_sqrt (show 0 ≤ 3 * k ^ 2 by positivity)
  have hden := Real.sq_sqrt (show 0 ≤ 2 + k ^ 2 by positivity)
  have hdenPos : 0 < Real.sqrt (2 + k ^ 2) := by positivity
  change 0.0044 < Real.sqrt (3 * k ^ 2) / Real.sqrt (2 + k ^ 2) ∧
    Real.sqrt (3 * k ^ 2) / Real.sqrt (2 + k ^ 2) < 0.0045
  rw [lt_div_iff₀ hdenPos, div_lt_iff₀ hdenPos]
  constructor
  · apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, hnum, hden]
    nlinarith only [hkloSq, hkhiSq]
  · apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, hnum, hden]
    nlinarith only [hkloSq, hkhiSq]

end PMConstants.WireMassBounds
