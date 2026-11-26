import PMConstants.FloorNeutrino
import PMConstants.Values

/-!
# Contextual neutrino scale

The floor and its sixfold response give exact model enclosures.
Exclusion theorems take comparison values and interval hypotheses as inputs.
The reporter supplies oscillation references from `Experimental.lean`.
A common rescaling does not derive a propagation Hamiltonian.
-/

noncomputable section
namespace PMElementaryParticles.NeutrinoContext
open PMConstants FloorNeutrino

def mRest : ℝ := Bulk.floorMass Values.alpha meEV

lemma sq_bounds : (0.009208 : ℝ) ^ 2 < mRest ^ 2 ∧ mRest ^ 2 < (0.009210 : ℝ) ^ 2 := by
  have hf := floor_bounds
  unfold mRest
  constructor <;> nlinarith [hf.1, hf.2]

theorem weak_minus_rest :
    (0.002967 : ℝ) < (6 * mRest) ^ 2 - mRest ^ 2 ∧ (6 * mRest) ^ 2 - mRest ^ 2 < 0.002969 := by
  obtain ⟨h1, h2⟩ := sq_bounds
  constructor <;> nlinarith

theorem weak_minus_rest_excluded {center uncertainty : ℝ} (hs : 0 < uncertainty)
    (hwindow : center + 17 * uncertainty ≤ 0.002967) :
    17 < ((6 * mRest) ^ 2 - mRest ^ 2 - center) / uncertainty := by
  obtain ⟨h, -⟩ := weak_minus_rest
  rw [lt_div_iff₀ hs]; linarith

theorem weak_squared_excluded {center uncertainty : ℝ} (hs : 0 < uncertainty)
    (hwindow : center + 20 * uncertainty ≤ 0.003052) :
    (0.003052 : ℝ) < (6 * mRest) ^ 2 ∧ (6 * mRest) ^ 2 < 0.003054 ∧
      20 < ((6 * mRest) ^ 2 - center) / uncertainty := by
  obtain ⟨h1, h2⟩ := sq_bounds
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  rw [lt_div_iff₀ hs]; nlinarith

/-- A comparison window can constrain the common multiplier. -/
theorem atmospheric_factor (k center : ℝ) (hk : 0 < k)
    (hfit : (k ^ 2 - 1) * mRest ^ 2 = center)
    (hlo : (5.55 ^ 2 - 1) * (0.009210 : ℝ) ^ 2 < center)
    (hhi : center < (5.57 ^ 2 - 1) * (0.009208 : ℝ) ^ 2) :
    5.55 < k ∧ k < 5.57 := by
  obtain ⟨h1, h2⟩ := sq_bounds
  constructor
  · by_contra h; push Not at h
    have hk2 : k ^ 2 ≤ 5.55 ^ 2 := by nlinarith
    have hm : 0 ≤ mRest ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hk2) hm]
  · by_contra h; push Not at h
    have hk2 : 5.57 ^ 2 ≤ k ^ 2 := by nlinarith
    have hm : 0 ≤ mRest ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hk2) hm]

end PMElementaryParticles.NeutrinoContext
