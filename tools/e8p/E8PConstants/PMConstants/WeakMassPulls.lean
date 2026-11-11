import PMConstants.WMassTest

/-!
# W-mass measured pulls (moved from the PMConstants leaf)

The scale-free clock ratio and its bounds stay in `PMConstants.WMassTest`; the
measured `m_Z` window and the labelled pulls live here.

With the measured `m_Z = 91.1876 ± 0.0021` GeV (comparison input),
`80.3827 < m_W < 80.38644` GeV (`w_window`). Pulls `(m_W − m)/σ` against
labelled comparison values (PDG review, 2025):

* world average without CDF, `80.3692 ± 0.0133`: between `1.0` and `1.3` (`pull_world`);
* CMS, `80.3602 ± 0.0099`: between `2.26` and `2.66` (`pull_cms`);
* CDF 2022, `80.4335 ± 0.0094`: below `−5.0` (`pull_cdf`); the clock ratio excludes it;
* Standard Model electroweak fit, `80.356 ± 0.006`: above `4.4` (`pull_sm`).

The clock ratio is therefore not the Standard Model value of the mixing: with the
measured Z mass it predicts `m_W` about 28 MeV above the electroweak fit, inside
the direct average at about one standard deviation, and 2.3–2.7σ above the single
most precise measurement. Correlations between experiments are not modelled.
-/

noncomputable section
namespace E8PConstants.WeakMassPulls
open PMConstants.WMassTest

theorem w_window {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    80.3827 < wMass mZ ∧ wMass mZ < 80.38644 := by
  have hr := ratio_bounds
  unfold wMass
  constructor
  · nlinarith [h.1, hr.1]
  · nlinarith [h.1, h.2, hr.1, hr.2]

/-- Pull of a value `x` against a comparison value `m ± σ`. -/
def pull (m σ x : ℝ) : ℝ := (x - m) / σ

theorem pull_world {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    1.0 < pull 80.3692 0.0133 (wMass mZ) ∧ pull 80.3692 0.0133 (wMass mZ) < 1.3 := by
  have hw := w_window h
  unfold pull
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem pull_cms {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    2.26 < pull 80.3602 0.0099 (wMass mZ) ∧ pull 80.3602 0.0099 (wMass mZ) < 2.66 := by
  have hw := w_window h
  unfold pull
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem pull_cdf {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    pull 80.4335 0.0094 (wMass mZ) < -5.0 := by
  have hw := w_window h
  unfold pull
  rw [div_lt_iff₀ (by norm_num)]; linarith

theorem pull_sm {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    4.4 < pull 80.356 0.006 (wMass mZ) := by
  have hw := w_window h
  unfold pull
  rw [lt_div_iff₀ (by norm_num)]; linarith

end E8PConstants.WeakMassPulls
