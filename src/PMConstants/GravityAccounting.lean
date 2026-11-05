import PMConstants.DepthEvents
import PMConstants.CertifiedConstants

/-!
# Which channel count the gravitational coupling can persist with

The residual capacity is `B_res = ν − χ/(σ − χ) − α = 16 − 2/3 − α` and `α_G = B_res α^{43/2}`
(`Depth.gravity`, with the attenuation from `DepthEvents`). `VevAccounting` found that the VEV
formula persists only when `ν` counts channels as frame (unit weight), not their payload content.
The gravitational coupling, measured to about `2.2·10⁻⁵`, tests the same question independently.

* `attenuation_bounds`: `1.143021965·10⁻⁴⁶ < α^{43/2} < 1.143021969·10⁻⁴⁶`.
* `channels_as_frame`: with `ν = 16`, `1.7517995·10⁻⁴⁵ < α_G < 1.7517996·10⁻⁴⁵`, inside the CODATA
  2022 window `(1.751770, 1.751849)·10⁻⁴⁵` (from `G = 6.67430(15)·10⁻¹¹`); about `−0.25σ`.
* `channels_as_payload`: counting the channels as stored payload, `16η`, gives `α_G < 1.7412·10⁻⁴⁵`,
  more than `200σ` below.

Two independent precision observables, the Fermi constant and Newton's constant, therefore pick the
same accounting: in both scale formulas `ν` is the channel frame, while in the per-phase footprint
the payload carried by those channels weighs `η`.
-/

noncomputable section
namespace PMConstants.GravityAccounting
open PMConstants CertifiedConstants

lemma rpow_eq_sqrt {a : ℝ} (ha : 0 ≤ a) : a ^ ((43 : ℝ) / 2) = Real.sqrt (a ^ 43) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num

theorem attenuation_bounds :
    (1.143021965e-46 : ℝ) < α ^ ((43 : ℝ) / 2) ∧ α ^ ((43 : ℝ) / 2) < 1.143021969e-46 := by
  have h := alpha_bounds
  have h0 : (0 : ℝ) ≤ α := by linarith [h.1]
  rw [rpow_eq_sqrt h0]
  have p1 : (0.007297352562 : ℝ) ^ 43 < α ^ 43 := pow_lt_pow_left₀ h.1 (by norm_num) (by norm_num)
  have p2 : α ^ 43 < (0.007297352563 : ℝ) ^ 43 := pow_lt_pow_left₀ h.2 h0 (by norm_num)
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    exact lt_trans (by norm_num) p1
  · rw [Real.sqrt_lt' (by norm_num)]
    exact lt_trans p2 (by norm_num)

theorem channels_as_frame :
    (1.7517995e-45 : ℝ) < Depth.gravity α ∧ Depth.gravity α < 1.7517996e-45 := by
  have h := alpha_bounds
  have hA := attenuation_bounds
  unfold Depth.gravity residual
  rw [PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.Delta_eq]
  constructor <;> nlinarith [h.1, h.2, hA.1, hA.2]

/-- Tight enclosure of the residual capacity `B_res`. -/
theorem residual_tight_bounds :
    (15.3260359807 : ℝ) < residual α ∧ residual α < 15.3260359808 := by
  have h := alpha_bounds
  unfold residual
  rw [PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq]
  constructor <;> linarith [h.1, h.2]

theorem inside_codata :
    (1.751770e-45 : ℝ) < Depth.gravity α ∧ Depth.gravity α < 1.751849e-45 := by
  have h := channels_as_frame; constructor <;> linarith [h.1, h.2]

def gravityPayload (a : ℝ) : ℝ :=
  ((PMSubstrate.E8Values.nu : ℝ) * overhead -
      (PMSubstrate.E8Values.chi : ℝ) /
        ((PMSubstrate.E8Values.sigma : ℝ) - (PMSubstrate.E8Values.chi : ℝ)) - a) *
    a ^ ((PMSubstrate.E8Values.Delta : ℝ) / (PMSubstrate.E8Values.chi : ℝ))

theorem channels_as_payload : gravityPayload α < 1.7412e-45 := by
  have h := alpha_bounds
  have hA := attenuation_bounds
  unfold gravityPayload overhead
  rw [PMSubstrate.E8Values.overhead_eq,
    PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq,
    PMSubstrate.E8Values.Delta_eq]
  nlinarith [h.1, h.2, hA.1, hA.2]

end PMConstants.GravityAccounting
