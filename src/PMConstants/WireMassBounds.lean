import PMAction.WireShiftedSpectrum
import PMAction.CarrierRateFromAdmittance
import PMConstants.CertifiedConstants
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A geometric bound for the bare wire benchmark

`ReferenceNode` fixes the restoring crossing against the in-cycle one at `k/K = α/2`, where
`NodeAmplitude` normalizes the in-cycle carrier to **admittance** `K = 1`. The wire's reference
row `(1, k, k)` is in **rates**. Two readings of `α/2` therefore exist, and they differ by a
factor of about ten.

* `bare_middle_heavy_bounds`, `shifted_middle_heavy_bound`: the **admittance reading**, which puts
  the probability `α/2` straight into the rate slot. `CarrierRateFromAdmittance` shows this is a
  category error.
* `kRate`, `kRate_bounds`, `rate_middle_heavy_bounds`: the **rate reading**. A transfer
  probability fixes a principal pulse area (`CertainTransferRate.principal_transfer_area`) and a
  rate is an area over a duration, so at a duration common to the restoring insertion and the
  certain crossing the ratio is `(2/π) arcsin √(α/2)`
  (`CarrierRateFromAdmittance.rate_ratio_common_duration`). That is about `0.0385`, ten and a half
  times the admittance reading.

Both are enclosures from the geometric value of `α` with no measured input. Which one the wire
wants is settled by `CarrierRateFromAdmittance`: the rate one, and with a duration ratio in front
of it when the two insertions do not last the same time.
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

/-- At the same benchmark coefficient, every normalized static insertion
strictly between zero and one leaves the middle-to-heavy ratio below 0.00730. -/
theorem shifted_middle_heavy_bound (s : ℝ) (hs : 0 < s) (hs₁ : s < 1) :
    let k := α / 2
    ∃ m₁ m₂ m₃ : ℝ, 0 < m₁ ∧ m₁ < m₂ ∧ m₂ < m₃ ∧ m₂ / m₃ < 0.00730 ∧
      ∀ m : ℝ, 0 ≤ m →
        (m ^ 2 ∈ spectrum ℝ (PMAction.WireResonanceSpectrum.gram k s) ↔
          m = m₁ ∨ m = m₂ ∨ m = m₃) := by
  intro k
  have hk : 0 < k := by dsimp [k]; linarith [alpha_bounds.1]
  have hk₁ : k < 1 := by dsimp [k]; linarith [alpha_bounds.2]
  obtain ⟨m₁, m₂, m₃, h₁, h₂, h₃, hratio, hspec⟩ :=
    PMAction.WireShiftedSpectrum.ordered_mass_spectrum k s hk hk₁ hs hs₁
  refine ⟨m₁, m₂, m₃, h₁, h₂, h₃, hratio.trans ?_, hspec⟩
  dsimp [k]
  linarith [alpha_bounds.2]

/-! ## The rate reading -/

/-- The restoring insertion's **rate** against the certain in-cycle crossing, at a common
duration: `(2/π) arcsin √(α/2)`. -/
def kRate : ℝ := PMAction.CarrierRateFromAdmittance.restoringRate (α / 2)

theorem sqrt_half_alpha_bounds :
    (0.060404 : ℝ) < Real.sqrt (α / 2) ∧ Real.sqrt (α / 2) < 0.060405 := by
  have ha := alpha_bounds
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; nlinarith [ha.1]
  · rw [Real.sqrt_lt' (by norm_num)]; nlinarith [ha.2]

/-- **Enclosure of the rate reading.** -/
theorem kRate_bounds : (0.03845 : ℝ) < kRate ∧ kRate < 0.03849 := by
  have hy := sqrt_half_alpha_bounds
  have hplo := Real.pi_gt_d20
  have hphi := Real.pi_lt_d20
  have hlo : (0.060404 : ℝ) < Real.arcsin (Real.sqrt (α / 2)) :=
    hy.1.trans (PMAction.CarrierRateFromAdmittance.lt_arcsin
      (by linarith [hy.1]) (by linarith [hy.2]))
  have hhi : Real.arcsin (Real.sqrt (α / 2)) < 0.06045 :=
    PMAction.CarrierRateFromAdmittance.arcsin_lt (by linarith [hy.1]) (by norm_num)
      (by linarith) (by nlinarith [hy.2])
  rw [kRate, PMAction.CarrierRateFromAdmittance.restoringRate,
    PMAction.CarrierRateFromAdmittance.area]
  constructor
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith

/-- **The bare wire at the rate reading.** The middle-to-heavy ratio is near `0.0471`, ten and a
half times the admittance reading's `0.0045`. -/
theorem rate_middle_heavy_bounds :
    let ratio := Real.sqrt (3 * kRate ^ 2) / Real.sqrt (2 + kRate ^ 2)
    0.0470 < ratio ∧ ratio < 0.0472 := by
  intro ratio
  have hk := kRate_bounds
  have hkloSq : (0.03845 : ℝ) ^ 2 ≤ kRate ^ 2 := pow_le_pow_left₀ (by norm_num) hk.1.le 2
  have hkhiSq : kRate ^ 2 ≤ (0.03849 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith [hk.1]) hk.2.le 2
  have hnum := Real.sq_sqrt (show 0 ≤ 3 * kRate ^ 2 by positivity)
  have hden := Real.sq_sqrt (show 0 ≤ 2 + kRate ^ 2 by positivity)
  have hdenPos : 0 < Real.sqrt (2 + kRate ^ 2) := by positivity
  change 0.0470 < Real.sqrt (3 * kRate ^ 2) / Real.sqrt (2 + kRate ^ 2) ∧
    Real.sqrt (3 * kRate ^ 2) / Real.sqrt (2 + kRate ^ 2) < 0.0472
  rw [lt_div_iff₀ hdenPos, div_lt_iff₀ hdenPos]
  constructor
  · apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, hnum, hden]
    nlinarith only [hkloSq, hkhiSq]
  · apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, hnum, hden]
    nlinarith only [hkloSq, hkhiSq]

end PMConstants.WireMassBounds
