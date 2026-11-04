import PMConstants.Matching
import PMConstants.RegulatoryBudget
import PMConstants.ResourceSelection
import Mathlib.Topology.Order.IntermediateValue

/-!
# Exact matching selects a feasible gain with spare capacity

For every positive aperture, `exp(-2g)/g = aperture` has a unique positive
solution. At the manuscript's aperture 6η, it lies strictly below the maximal
budget gain 128/989. It satisfies the capacity inequality with strictly positive
slack. Exact matching and maximal gain therefore cannot both hold for the
uncorrected baseline model. No physical correction term is invented here.
-/

noncomputable section
namespace PMConstants.MatchedRegulation
open Matching

theorem regulator_continuousOn {a b : ℝ} (ha : 0 < a) :
    ContinuousOn regulator (Set.Icc a b) := by
  apply ContinuousOn.div
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  · exact continuous_id.continuousOn
  · intro x hx
    exact (ha.trans_le hx.1).ne'

/-- Existence is a mathematical property of the proposed interface law, not a
derivation of that law from the E8 substrate. -/
theorem positive_match_exists {aperture : ℝ} (hA : 0 < aperture) :
    ∃ gain : ℝ, 0 < gain ∧ regulator gain = aperture := by
  let a : ℝ := 1/(aperture+3)
  let b : ℝ := 1/aperture
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact one_div_le_one_div_of_le hA (by linarith)
  have hlo : aperture ≤ regulator a := by
    have h := Real.add_one_le_exp (-2*a)
    have hinv : 1/a = aperture+3 := by dsimp [a]; field_simp
    have hbound : 1/a-2 ≤ regulator a := by
      apply (le_div_iff₀ ha).mpr
      have hx : (1/a-2)*a = 1-2*a := by field_simp
      rw [hx]
      linarith
    rw [hinv] at hbound
    linarith
  have hhi : regulator b ≤ aperture := by
    have hexp : Real.exp (-2*b) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hinv : 1/b = aperture := by dsimp [b]; field_simp
    calc
      regulator b ≤ 1/b := (div_le_div_iff_of_pos_right hb).mpr hexp
      _ = aperture := hinv
  obtain ⟨gain, hgain, heq⟩ :=
    intermediate_value_Icc' hab (regulator_continuousOn ha) ⟨hhi, hlo⟩
  exact ⟨gain, ha.trans_le hgain.1, heq⟩

theorem positive_match_exists_unique {aperture : ℝ} (hA : 0 < aperture) :
    ∃! gain : ℝ, 0 < gain ∧ regulator gain = aperture := by
  obtain ⟨g, hg, hm⟩ := positive_match_exists hA
  refine ⟨g, ⟨hg, hm⟩, ?_⟩
  intro g' hg'
  exact matching_unique hg'.1 hg hg'.2 hm

/-- The matching solution is below the independently prescribed gain. -/
theorem match_below_baseline {gain : ℝ} (_hg : 0 < gain)
    (hm : regulator gain = 6*overhead) : gain < selfCoupling := by
  by_contra h
  have hle : selfCoupling ≤ gain := le_of_not_gt h
  rcases hle.eq_or_lt with heq | hlt
  · have hbad := baseline_not_exact_match
    rw [heq] at hbad
    exact hbad hm
  · have hstrict := regulator_strict self_coupling_pos hlt
    have hgap := baseline_matching_gap.1
    rw [hm] at hstrict
    linarith

theorem matched_feasible_exists_unique :
    ∃! gain : ℝ, 0 < gain ∧ RegulatoryBudget.Feasible 23 3 (1/43) gain ∧
      regulator gain = 6*overhead := by
  have hA : 0 < 6*overhead := by norm_num [overhead]
  obtain ⟨g, hg, hm⟩ := positive_match_exists hA
  have hlt := match_below_baseline hg hm
  refine ⟨g, ⟨hg, (RegulatoryBudget.scalar_feasible_iff _).mpr ⟨hg.le, hlt.le⟩, hm⟩, ?_⟩
  intro g' hg'
  exact matching_unique hg'.1 hg hg'.2.2 hm

theorem match_leaves_positive_slack {gain : ℝ} (hg : 0 < gain)
    (hm : regulator gain = 6*overhead) : 0 < 3-(23*gain+1/43) := by
  have hlt := match_below_baseline hg hm
  norm_num [selfCoupling] at hlt
  linarith

theorem no_maximal_exact_match {gain : ℝ}
    (hmax : RegulatoryBudget.Maximal 23 3 (1/43) gain) :
    regulator gain ≠ 6*overhead := by
  rw [(RegulatoryBudget.scalar_maximal_iff _).mp hmax]
  exact baseline_not_exact_match

theorem no_process_exact_match (p : ResourceSelection.Process) :
    regulator p.gain ≠ 6*overhead := by
  rw [ResourceSelection.scalar_forced p]
  exact baseline_not_exact_match

theorem regulator_as_inverse (g : ℝ) :
    regulator g = 1 / (Real.exp (2*g) * g) := by
  rw [regulator, show -2*g = -(2*g) by ring, Real.exp_neg]
  simp [div_eq_mul_inv, mul_comm]

/-- Rigorous endpoint comparisons for the matching solution. -/
theorem matching_endpoints :
    6*overhead < regulator 0.1294121 ∧ regulator 0.1294122 < 6*overhead := by
  constructor
  · rw [regulator_as_inverse]
    apply (lt_div_iff₀ (by positivity)).mpr
    have h := Real.exp_bound' (x := 2*0.1294121) (by norm_num) (by norm_num)
      (n := 8) (by decide)
    norm_num [Finset.sum_range_succ, overhead] at h ⊢
    nlinarith
  · rw [regulator_as_inverse]
    apply (div_lt_iff₀ (by positivity)).mpr
    have h := Real.sum_le_exp_of_nonneg (x := 2*0.1294122) (by norm_num) 8
    norm_num [Finset.sum_range_succ, overhead] at h ⊢
    nlinarith

theorem matched_gain_bounds {gain : ℝ} (hg : 0 < gain)
    (hm : regulator gain = 6*overhead) :
    0.1294121 < gain ∧ gain < 0.1294122 := by
  obtain ⟨hL, hU⟩ := matching_endpoints
  constructor
  · by_contra h
    rcases (le_of_not_gt h).eq_or_lt with heq | hlt
    · rw [← heq, hm] at hL; exact lt_irrefl _ hL
    · have hs := regulator_strict hg hlt
      rw [hm] at hs
      linarith
  · by_contra h
    rcases (le_of_not_gt h).eq_or_lt with heq | hlt
    · rw [heq, hm] at hU; exact lt_irrefl _ hU
    · have hs := regulator_strict (show (0 : ℝ) < 0.1294122 by norm_num) hlt
      rw [hm] at hs
      linarith

end PMConstants.MatchedRegulation
