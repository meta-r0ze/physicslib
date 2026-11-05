import PMConstants.General.Matching
import PMConstants.Matching

/-! Apply the general reflected-load criterion to the stated Higgs/aperture
comparison. The required reserve is calculated, not set by a fitted tolerance.
Comparing it to Margin is arithmetic; making Margin available to this interface
is an additional allocation premise, including its cost elsewhere in the ledger.
-/
noncomputable section
namespace PMConstants.SurfaceBudget
open ElectroweakE8

def source : ℝ := Matching.regulator selfCoupling
def load : ℝ := 6*overhead
def amplitude : ℝ := Interface.reflection source load
def fraction : ℝ := General.Matching.reflected 1 source load

theorem source_positive : 0 < source := by
  exact div_pos (Real.exp_pos _) self_coupling_pos

theorem amplitude_bounds : (1/24000 : ℝ) < amplitude ∧ amplitude < 1/10000 := by
  have hg := Matching.baseline_matching_gap
  have hload : load = 513/86 := by norm_num [load, overhead]
  have hgap : (1/2000 : ℝ) < load-source ∧ load-source < 1/1000 := hg
  have hsum : 10 < load+source ∧ load+source < 12 := by
    constructor <;> linarith [hgap.1, hgap.2]
  have hd : 0 < load+source := by linarith [hsum.1]
  unfold amplitude Interface.reflection
  constructor
  · apply (lt_div_iff₀ hd).mpr; nlinarith [hgap.1, hsum.2]
  · apply (div_lt_iff₀ hd).mpr; nlinarith [hgap.2, hsum.1]

theorem reflected_bounds : (0.000000001 : ℝ) < fraction ∧ fraction < 0.00000001 := by
  have h := amplitude_bounds
  change (0.000000001 : ℝ) < 1*amplitude^2 ∧ 1*amplitude^2 < 0.00000001
  constructor <;> nlinarith [h.1, h.2]

theorem transmission_lower_bound : (0.99999999 : ℝ) < Interface.transmission source load := by
  have h := reflected_bounds.2
  unfold fraction General.Matching.reflected at h
  unfold Interface.transmission
  nlinarith

theorem reflected_smaller_than_margin : fraction < bareYukawa := by
  have h := reflected_bounds.2
  norm_num [bareYukawa]
  linarith

/-- This is conditional on the reserve P*Margin actually being available;
the theorem does not allocate that reserve or derive the interface law. -/
theorem admissible_if_margin_available {P B : ℝ} (hP : 0 ≤ P) (hB : P*bareYukawa ≤ B) :
    General.Matching.Admissible P B source load := by
  have h := mul_le_mul_of_nonneg_left reflected_smaller_than_margin.le hP
  unfold General.Matching.Admissible General.Matching.reflected
  unfold fraction General.Matching.reflected at h
  nlinarith

/-- Maximal scalar gain leaves no reserve in the specified 23-label ledger.
The positive reflected load cannot be charged there without changing that ledger. -/
theorem maximal_scalar_budget_has_no_reserve :
    ¬ General.Matching.Admissible 1 (3-(23*selfCoupling+1/43)) source load := by
  have h := reflected_bounds.1
  change ¬ fraction ≤ 3-(23*selfCoupling+1/43)
  norm_num [selfCoupling]
  linarith

end PMConstants.SurfaceBudget
