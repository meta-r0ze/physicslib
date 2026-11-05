import PMFlavor.CPPhases
import PMFlavor.TriangleAngles
import PMFlavor.TriangleGamma

/-!
# Experimental comparison leaf

This module collects the fixed PDG/LHCb/NuFIT benchmark comparisons. It is a
comparison leaf: the derivation modules (`CPPhases`, `TriangleAngles`,
`TriangleGamma`) do not import it. No measured number here enters a theorem
statement used by the model derivation.

* `δ_vs_gamma` — proxy delta pull against LHCb's 2024 gamma combination.
* `nu_phase` — the proposed leptonic phase against NuFIT 6.0.
* `sin2β_pull` — the geometric `sin 2β` against the PDG/HFLAV value.
* `gamma_pull` — the actual matrix triangle angle against the LHCb value.
-/

noncomputable section
namespace PMFlavor.ExperimentalPulls
open Real CPPhases TriangleAngles TriangleGamma

/-- The leptonic phase `360°/φ`. -/
def nuDeg : ℝ := 360 / ((1 + √5) / 2)

theorem δ_vs_gamma : 1.28 < (δdeg - 64.6) / 2.8 ∧ (δdeg - 64.6) / 2.8 < 1.29 ∧
    |δdeg - 68| / 5 < 0.05 := by
  have h := δ_degrees
  refine ⟨by rw [lt_div_iff₀ (by norm_num)]; linarith,
    by rw [div_lt_iff₀ (by norm_num)]; linarith, ?_⟩
  rw [abs_of_pos (by linarith), div_lt_iff₀ (by norm_num)]; linarith

theorem nu_phase : (222.492 : ℝ) < nuDeg ∧ nuDeg < 222.493 ∧
    0.94 < (nuDeg - 197) / 27 ∧ (nuDeg - 197) / 27 < 0.95 := by
  have s1 : (2.236067 : ℝ) < √5 := by rw [lt_sqrt (by norm_num)]; norm_num
  have s2 : √5 < (2.236068 : ℝ) := by rw [sqrt_lt' (by norm_num)]; norm_num
  have e : nuDeg = 180 * (√5 - 1) := by
    unfold nuDeg
    have h5 : (√5)^2 = 5 := sq_sqrt (by norm_num)
    have hp : (1 + √5) ≠ 0 := by positivity
    field_simp; nlinarith [h5]
  rw [e]
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem sin2β_pull : -0.75 < (sin2β - 0.710) / 0.011 ∧
    (sin2β - 0.710) / 0.011 < -0.69 := by
  obtain ⟨h1, h2⟩ := sin2β_bounds
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem gamma_pull :
    1.27 < (value * 180 / Real.pi - 64.6) / 2.8 ∧
      (value * 180 / Real.pi - 64.6) / 2.8 < 1.28 := by
  have h := gamma_degrees
  constructor
  · apply (lt_div_iff₀ (by norm_num : 0 < (2.8 : ℝ))).mpr
    linarith [h.1]
  · apply (div_lt_iff₀ (by norm_num : 0 < (2.8 : ℝ))).mpr
    linarith [h.2]

end PMFlavor.ExperimentalPulls
