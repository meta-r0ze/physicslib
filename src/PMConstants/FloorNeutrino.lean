import PMConstants.Bulk
import PMConstants.CertifiedConstants
import PMSubstrate.SIUnits

/-!
# Bare thermal tower and common-scale splitting obstruction

The original bounds apply when Bulk.floorMass is directly identified with the
largest propagation mass. Papers V/VI also propose a factor-six interaction
response; that extra proposal is not tested by the bare-mass upper bound alone.

The added tower identities show that any single common multiplier leaves the
ratio of adjacent squared-mass splittings at 43²=1849. All three pairwise gaps
are proportional to (1,1849,1850), so no ratio of two gaps lies between 2 and
1000. This is an exact arithmetic obstruction to identifying a uniformly scaled
three-state tower with the observed two oscillation scales. It does not exclude
a different propagation Hamiltonian or a nonuniform, derived response law.

External oscillation data are comparison inputs, not E8 consequences. The
vacuum-density interpretation of the thermal floor is a separate identification.
-/

noncomputable section
namespace PMConstants.FloorNeutrino
open PMConstants CertifiedConstants

def meEV : ℝ := PMSubstrate.SIUnits.electronMassEV

theorem floor_bounds : 0.009208 < Bulk.floorMass α meEV ∧ Bulk.floorMass α meEV < 0.009210 := by
  have ha := alpha_bounds
  have hp1 := Real.pi_gt_d6; have hp2 := Real.pi_lt_d6
  unfold Bulk.floorMass Bulk.floorRatio meEV PMSubstrate.SIUnits.electronMassEV
  rw [PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.Delta_eq]
  constructor <;> nlinarith [mul_pos (by linarith : (0:ℝ) < Real.pi) (by linarith : (0:ℝ) < α)]

theorem tower_sum :
    Bulk.floorMass α meEV + Bulk.floorMass α meEV / 43 + Bulk.floorMass α meEV / 43^2 < 0.0095 := by
  have h := floor_bounds; nlinarith [h.2]

theorem oscillation_excludes (n : ℕ) :
    (Bulk.floorMass α meEV / 43^n)^2 < 0.000085 ∧ (0.000085 : ℝ) < 0.0024 := by
  have h := floor_bounds
  have hpos : 0 < Bulk.floorMass α meEV := by linarith [h.1]
  have hle : Bulk.floorMass α meEV / 43^n ≤ Bulk.floorMass α meEV :=
    div_le_self hpos.le (one_le_pow₀ (by norm_num))
  have hnn : 0 ≤ Bulk.floorMass α meEV / 43^n := by positivity
  refine ⟨?_, by norm_num⟩
  nlinarith [h.2]

/-- A common response scale, including the proposed factor six. -/
def towerMass (base scale : ℝ) (n : ℕ) : ℝ := scale*base/(PMSubstrate.E8Values.Delta : ℝ)^n

def smallGap (base scale : ℝ) : ℝ := (towerMass base scale 1)^2-(towerMass base scale 2)^2
def largeGap (base scale : ℝ) : ℝ := (towerMass base scale 0)^2-(towerMass base scale 1)^2

lemma small_gap_formula (base scale : ℝ) :
    smallGap base scale=(scale*base)^2*(1848/3418801) := by
  norm_num [smallGap, towerMass]
  ring

lemma large_gap_formula (base scale : ℝ) :
    largeGap base scale=(scale*base)^2*(1848/1849) := by
  norm_num [largeGap, towerMass]
  ring

theorem splitting_identity (base scale : ℝ) : largeGap base scale=1849*smallGap base scale := by
  rw [small_gap_formula, large_gap_formula]
  ring

lemma small_gap_pos {base scale : ℝ} (h : scale*base ≠ 0) : 0 < smallGap base scale := by
  rw [small_gap_formula]
  exact mul_pos (sq_pos_of_ne_zero h) (by norm_num)

/-- Rescaling all three masses cannot change the splitting hierarchy. -/
theorem splitting_ratio (base scale : ℝ) (h : scale*base ≠ 0) :
    largeGap base scale/smallGap base scale=1849 := by
  rw [splitting_identity]
  exact mul_div_cancel_right₀ _ (small_gap_pos h).ne'

/-- All positive pairwise squared-mass differences, allowing arbitrary relabeling. -/
def gaps (base scale : ℝ) : Fin 3 → ℝ :=
  ![smallGap base scale,largeGap base scale,smallGap base scale+largeGap base scale]

lemma gaps_proportional (base scale : ℝ) :
    gaps base scale=smallGap base scale • (![1,1849,1850] : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> simp [gaps, splitting_identity] <;> ring

/-- Even a relabeling cannot produce a moderate hierarchy from a common-scale tower. -/
theorem no_moderate_gap_ratio (base scale : ℝ) (h : scale*base ≠ 0) (i j : Fin 3) :
    ¬ (2 < gaps base scale i/gaps base scale j ∧ gaps base scale i/gaps base scale j < 1000) := by
  have hn := (small_gap_pos h).ne'
  have he : gaps base scale i/gaps base scale j =
      ((![1,1849,1850] : Fin 3 → ℝ) i)/((![1,1849,1850] : Fin 3 → ℝ) j) := by
    rw [gaps_proportional]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_div_mul_left _ _ hn
  rw [he]
  fin_cases i <;> fin_cases j <;> norm_num

/-- The proposed factor-six response is tested separately from the bare floor. -/
theorem factor_six_windows :
    0.00000164 < smallGap (Bulk.floorMass α meEV) 6 ∧
    smallGap (Bulk.floorMass α meEV) 6 < 0.00000166 ∧
    0.00304 < largeGap (Bulk.floorMass α meEV) 6 ∧
    largeGap (Bulk.floorMass α meEV) 6 < 0.00306 := by
  have hf := floor_bounds
  have hlo : (0.009208 : ℝ)^2 < (Bulk.floorMass α meEV)^2 := by
    have hp := mul_pos (by linarith [hf.1] : 0 < Bulk.floorMass α meEV-0.009208)
      (by linarith [hf.1] : 0 < Bulk.floorMass α meEV+0.009208)
    nlinarith
  have hhi : (Bulk.floorMass α meEV)^2 < (0.009210 : ℝ)^2 := by
    have hp := mul_pos (by linarith [hf.2] : 0 < 0.009210-Bulk.floorMass α meEV)
      (by linarith [hf.1] : 0 < 0.009210+Bulk.floorMass α meEV)
    nlinarith
  rw [small_gap_formula, large_gap_formula]
  constructor
  · nlinarith
  · constructor
    · nlinarith
    · constructor <;> nlinarith

end PMConstants.FloorNeutrino
