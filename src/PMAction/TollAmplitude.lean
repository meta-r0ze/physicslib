import PersistenceMechanics.EffectiveAction
import PersistenceMechanics.Gibbs
import PMSubstrate.NetCost
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# From a scheduled Toll to a wire amplitude

A schedule of comparisons charges each label a Toll: the expected number of comparisons that
register on it, `T = floor + Σᵢ wᵢ fᵢ` with flag probabilities `fᵢ`
(`Machine.InterferenceReadout.flagProbability`, `CommonResponse.stateFlag`). This module derives
how that Toll sets the amplitude the label keeps on the wire.

**The form.** Paper I fixes it. Costs add as expected transition counts, so a probability enters
as itself (`PMSubstrate.NetCost.expected_count_linear`), and survival exponentiates the sum once
(`NetCost.survival_factorizes`, `PersistenceMechanics.HazardForm`). The amplitude carries half
the attenuation (`PersistenceMechanics.EffectiveAction.amplitude_normSq`). So the weight is
`exp(−k T)` and the amplitude `exp(−k T/2)` for one scale `k = β c₀`.

**The scale.** Split the schedule into `N` independent sub-comparisons with the same expected
count `T`, each registering with probability `T/N`. Let a registration be survived with
probability `q`. The exact probability that the branch survives every sub-comparison is
`(1 − (1 − q) T/N)^N`, and this tends to `exp(−(1 − q) T)` (`rare_registration_limit`). So the
one scale that agrees with the actual statistics of rare registrations is `k = 1 − q`
(`scale_of_limit`). A branch on which a comparison registers is flagged and repaired; it is no
longer the unflagged wire amplitude, so `q = 0` and `k = 1` (`unflagged_scale`). With Closure's
`c₀ = 1` this sets `β c₀ = 1`: the Toll is counted in expected registrations and needs no further
unit.

* At unit scale, use `EffectiveAction.attenuationWeight 1 T` and `Gibbs.weight 1 T`.
  `wireAmplitude_sq` relates the amplitude to the survival weight.
* `amplitude_ratio`: a common floor cancels; only Toll differences set amplitude ratios.
* `ratio_ge_iff`: `s_x ≥ r s_y` exactly when `T_y − T_x ≥ 2 log r`. A factor of two between two
  labels is a Toll difference of `2 log 2`, not a structural bound.
* `schedule_factorizes`: the amplitude of a schedule is the product of per-comparison factors.
* `not_affine`: the conversion is not affine in the Toll (`1 + e⁻¹ > 2e^{−1/2}`). So bounds
  proved for affine conversions (`PMElementaryParticles.ProtocolToll.hyperchargeFlag_schedule_bound`)
  do not constrain it.
* `retained_below_survival`: a single retained no-flag port keeps weight `1 − f`, strictly below
  `exp(−f)` for `f ≠ 0`. The port product counts `−log(1 − f)` per comparison, not `f`; it agrees
  with the survival form only for rare registrations (`rare_registration_limit` at `N = 1` versus
  `N → ∞`). NetCost's linearity selects the survival form.

Premise: the wire amplitude of a label is the amplitude of its unflagged branch. Not derived
here: the schedule (which comparisons, steps and counts act on which labels).
-/

noncomputable section
namespace PMAction.TollAmplitude
open Real Filter Topology
open PersistenceMechanics.EffectiveAction (attenuationWeight)

/-- **Rare registrations.** `N` independent sub-comparisons with total expected count `T`, each
registration survived with probability `q`: the survival `(1 − (1 − q)T/N)^N` tends to
`exp(−(1 − q)T)`. -/
theorem rare_registration_limit (q T : ℝ) :
    Tendsto (fun N : ℕ => (1 - (1 - q) * T / N) ^ N) atTop (𝓝 (exp (-((1 - q) * T)))) := by
  have h := Real.tendsto_one_add_div_pow_exp (-((1 - q) * T))
  refine h.congr fun N => ?_
  ring_nf

/-- **The scale is fixed by the limit.** If Paper I's survival `exp(−k T)` is the rare-registration
limit at some nonzero Toll, then `k = 1 − q`. -/
theorem scale_of_limit {k q T : ℝ} (hT : T ≠ 0)
    (h : Tendsto (fun N : ℕ => (1 - (1 - q) * T / N) ^ N) atTop (𝓝 (exp (-k * T)))) :
    k = 1 - q := by
  have he := tendsto_nhds_unique h (rare_registration_limit q T)
  have hl : -k * T = -((1 - q) * T) := exp_injective he
  have : (k - (1 - q)) * T = 0 := by linarith
  rcases mul_eq_zero.mp this with h0 | h0
  · linarith
  · exact absurd h0 hT

/-- **The unflagged branch has unit scale.** A registration flags the branch, so the unflagged
amplitude survives none (`q = 0`): `k = 1`. -/
theorem unflagged_scale {k T : ℝ} (hT : T ≠ 0)
    (h : Tendsto (fun N : ℕ => (1 - (1 - 0) * T / N) ^ N) atTop (𝓝 (exp (-k * T)))) :
    k = 1 := by
  simpa using scale_of_limit (q := 0) hT h

/-- The unit-scale attenuation remains positive at every Toll. -/
theorem wireAmplitude_pos (T : ℝ) : 0 < attenuationWeight 1 T := exp_pos _

/-- The amplitude squared is the survival weight. -/
theorem wireAmplitude_sq (T : ℝ) : attenuationWeight 1 T ^ 2 = PersistenceMechanics.Gibbs.weight 1 T := by
  rw [attenuationWeight, PersistenceMechanics.Gibbs.weight, sq, ← exp_add]
  ring_nf

/-- Lower Toll, larger amplitude. -/
theorem wireAmplitude_lt_iff {a b : ℝ} : attenuationWeight 1 a < attenuationWeight 1 b ↔ b < a := by
  unfold attenuationWeight
  rw [exp_lt_exp]
  constructor <;> intro h <;> linarith

/-- **A common floor cancels.** -/
theorem amplitude_ratio (floor Tx Ty : ℝ) :
    attenuationWeight 1 (floor + Tx) / attenuationWeight 1 (floor + Ty) = exp (-(Tx - Ty) / 2) := by
  unfold attenuationWeight
  rw [← exp_sub]
  ring_nf

/-- **Ratios are Toll differences.** For `r > 0`, `s_x ≥ r s_y` exactly when
`T_y − T_x ≥ 2 log r`. -/
theorem ratio_ge_iff {r Tx Ty : ℝ} (hr : 0 < r) :
    r * attenuationWeight 1 Ty ≤ attenuationWeight 1 Tx ↔ 2 * log r ≤ Ty - Tx := by
  unfold attenuationWeight
  rw [← exp_log hr, ← exp_add, exp_le_exp, exp_log hr]
  constructor <;> intro h <;> linarith

/-- A schedule's Toll: a floor plus weighted flag probabilities. -/
def weightedFlagCost {ι : Type*} [Fintype ι] (floor : ℝ) (w f : ι → ℝ) : ℝ :=
  floor + ∑ i, w i * f i

/-- **The amplitude factorizes over the schedule.** -/
theorem schedule_factorizes {ι : Type*} [Fintype ι] (floor : ℝ) (w f : ι → ℝ) :
    attenuationWeight 1 (weightedFlagCost floor w f) =
      attenuationWeight 1 floor * ∏ i, attenuationWeight 1 (w i * f i) := by
  simp only [attenuationWeight, weightedFlagCost, one_mul]
  rw [← exp_sum, ← exp_add]
  congr 1
  have h : (∑ i, -(w i * f i) / 2) = -(∑ i, w i * f i) / 2 := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
  rw [h]
  ring

/-- **Not affine.** The midpoint of two Tolls has a smaller amplitude than the mean of their
amplitudes: `2 e^{−1/2} < 1 + e⁻¹`. -/
theorem not_affine : 2 * attenuationWeight 1 1 < attenuationWeight 1 0 + attenuationWeight 1 2 := by
  unfold attenuationWeight
  have h : (0 : ℝ) < (1 - exp (-1 / 2)) ^ 2 := by
    have hlt : exp (-1 / 2) < 1 := by
      have := exp_lt_exp.mpr (show (-1 / 2 : ℝ) < 0 by norm_num)
      simpa using this
    positivity
  have hsq : exp (-1 / 2) ^ 2 = exp (-2 / 2) := by rw [sq, ← exp_add]; ring_nf
  norm_num at hsq ⊢
  nlinarith [hsq]

/-- No affine map of the Toll equals the wire amplitude. -/
theorem no_affine_form : ¬ ∃ A B : ℝ, ∀ T, attenuationWeight 1 T = A + B * T := by
  rintro ⟨A, B, h⟩
  have := not_affine
  rw [h 0, h 1, h 2] at this
  linarith

/-- **The retained port lies below survival.** One retained no-flag port keeps `1 − f`, and
`1 − f < exp(−f)` for `f ≠ 0`. -/
theorem retained_below_survival {f : ℝ} (hf : f ≠ 0) : 1 - f < PersistenceMechanics.Gibbs.weight 1 f := by
  have := add_one_lt_exp (neg_ne_zero.mpr hf)
  simp only [PersistenceMechanics.Gibbs.weight, neg_mul, one_mul]
  linarith

end PMAction.TollAmplitude
