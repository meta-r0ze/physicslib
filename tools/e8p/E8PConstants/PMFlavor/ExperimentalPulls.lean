import PMFlavor.Values

/-!
# Experimental comparison leaf

Fixed PDG/LHCb benchmark comparisons of `PMFlavor.Values` (`ckmDeltaDeg`, `sin2Beta`, `gammaDeg`).
No measured number here enters a theorem used by the derivation.

* `δ_vs_gamma` — the CKM phase against LHCb's 2024 `γ` combination (and the older `68 ± 5°`).
* `sin2β_pull` — `sin 2β` against PDG 2024 (`0.709 ± 0.011`).
* `gamma_pull` — the matrix's triangle angle `γ` against LHCb.

(The leptonic phase `360°/φ` once compared here was retired, `ReferenceFlavour`; the derived PMNS
phase has no degree enclosure in `Values` yet.)
-/

noncomputable section
namespace E8PConstants.ExperimentalPulls
open PMFlavor.Values

theorem δ_vs_gamma : 1.28 < (ckmDeltaDeg - 64.6) / 2.8 ∧ (ckmDeltaDeg - 64.6) / 2.8 < 1.29 ∧
    |ckmDeltaDeg - 68| / 5 < 0.05 := by
  have h := ckmDeltaDeg_bounds
  refine ⟨by rw [lt_div_iff₀ (by norm_num)]; linarith,
    by rw [div_lt_iff₀ (by norm_num)]; linarith, ?_⟩
  rw [abs_of_pos (by linarith), div_lt_iff₀ (by norm_num)]; linarith

theorem sin2β_pull : -0.65 < (sin2Beta - 0.709) / 0.011 ∧
    (sin2Beta - 0.709) / 0.011 < -0.60 := by
  obtain ⟨h1, h2⟩ := sin2Beta_bounds
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem gamma_pull :
    1.27 < (gammaDeg - 64.6) / 2.8 ∧ (gammaDeg - 64.6) / 2.8 < 1.28 := by
  have h := gammaDeg_bounds
  constructor
  · apply (lt_div_iff₀ (by norm_num : 0 < (2.8 : ℝ))).mpr
    linarith [h.1]
  · apply (div_lt_iff₀ (by norm_num : 0 < (2.8 : ℝ))).mpr
    linarith [h.2]

end ExperimentalPulls
