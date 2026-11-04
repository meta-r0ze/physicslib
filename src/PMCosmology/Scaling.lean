import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Conditional arithmetic and saturation identities, not a perturbation or
Einstein-equation derivation. Empirical anchors are external inputs. -/
noncomputable section
namespace PMCosmology

def scalarIndex : ℝ := 1-1/32
def loadFactor : ℝ := 1+1/32+2/43+1/172
def darkRatio : ℝ := 248/48

theorem exact_ratios : scalarIndex=31/32 ∧ loadFactor=1491/1376 ∧ darkRatio=31/6 := by
  norm_num [scalarIndex, loadFactor, darkRatio]

theorem load_gt_one : 1 < loadFactor := by norm_num [loadFactor]

theorem loaded_hubble_larger {H : ℝ} (hH : 0 < H) : H < H*loadFactor := by
  have := load_gt_one
  nlinarith

theorem loaded_clustering_smaller {S : ℝ} (hS : 0 < S) : S/loadFactor < S := by
  apply (div_lt_iff₀ (by norm_num [loadFactor] : 0 < loadFactor)).mpr
  have := load_gt_one
  nlinarith

theorem joint_rescaling_invariant (H S : ℝ) :
    (H*loadFactor)*(S/loadFactor) = H*S := by
  have h : loadFactor ≠ 0 := by norm_num [loadFactor]
  field_simp

/-- The dimensional anchor is still required: 23/43 alone has no Hubble units. -/
theorem base_hubble_ratio : (23 : ℝ)/43 > 0 := by norm_num

def refractiveIndex (capacity occupancy : ℝ) : ℝ := capacity/(capacity-occupancy)

theorem index_at_least_one {C K : ℝ} (_hC : 0 < C) (hK : 0 ≤ K) (hlt : K < C) :
    1 ≤ refractiveIndex C K := by
  unfold refractiveIndex
  apply (le_div_iff₀ (by linarith : 0 < C-K)).mpr
  linarith

theorem index_increases {C a b : ℝ} (hC : 0 < C) (ha : a ≤ b) (hb : b < C) :
    refractiveIndex C a ≤ refractiveIndex C b := by
  unfold refractiveIndex
  apply (div_le_div_iff₀ (by linarith : 0 < C-a) (by linarith : 0 < C-b)).mpr
  nlinarith

/-- Arbitrarily large finite index below capacity; division at saturation is
not used as a representation of an infinite horizon. -/
theorem unbounded_below_capacity {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    ∃ K, 0 ≤ K ∧ K < C ∧ B < refractiveIndex C K := by
  refine ⟨C-C/(B+1), ?_, ?_, ?_⟩
  · have hden : 0 < B+1 := by linarith
    have hdiv : C/(B+1) ≤ C := (div_le_iff₀ hden).mpr (by nlinarith)
    linarith
  · have := div_pos hC (by linarith : 0 < B+1)
    linarith
  · have heq : refractiveIndex C (C-C/(B+1)) = B+1 := by
      unfold refractiveIndex
      have hc : C ≠ 0 := ne_of_gt hC
      have hb : B+1 ≠ 0 := by linarith
      field_simp
      ring
    rw [heq]
    linarith

/-- If active modes are a subset of the total, the inactive/active ratio
subtracts the active sector first; total/active differs by one. -/
theorem disjoint_dark_count_check :
    ((248 : ℝ)-48)/48 = 25/6 ∧ darkRatio = 1+25/6 := by
  norm_num [darkRatio]

end PMCosmology
