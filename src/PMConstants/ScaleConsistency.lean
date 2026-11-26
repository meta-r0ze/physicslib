import PMConstants.ElectroweakBounds

/-!
# One interface scale for all couplings?

The proposed couplings all read out the same geometric admittance `α`. A response law
mapping the substrate to the electroweak interface would replace `α` by `k PMSubstrate.causalCoupling` with one
interface factor `k`, keeping the VEV. This module tests that minimal response family
against the two comparison inputs the paper already uses: the Z-mass anchor of its W
calculator and the strong-coupling window at the Z pole. These are labelled comparison
inputs, not derived numbers.

* `z_needs_factor`: matching the Z anchor requires `1.0362 < k < 1.0365`.
* `same_scale_obstruction`: the same `k` puts the strong readout above `0.1221`, outside
  the window. No single interface factor serves both readouts.
* `ratio_every_scale`, `anchored_w`: the mass ratio `m_W² = (1−s) m_Z²` holds for every `k`;
  with the Z anchor it gives `80.3845 < m_W < 80.3846`.
* `closure_exact`, `closure_coefficient`: defining the Yukawa by the mass law from the VEV
  closes the electron relation exactly; written as `y_bare (1 + c PMSubstrate.causalCoupling)` it needs
  `1.28777 < c < 1.28779`, so the stated `σ/D = 5/4` dressing is excluded.

The measured comparison proofs are in `tools/e8p/E8PConstants/PMConstants/ScaleComparisons.lean`.
-/

noncomputable section
namespace PMConstants.ScaleConsistency
open ElectroweakE8 CertifiedConstants JointConstants GaugeSpectrum ElectroweakBounds

/-! ## Gauge readouts with one interface factor -/

theorem ratio_every_scale (k : ℝ) :
    k * wMassSquared PMSubstrate.causalCoupling electronGeV = (1 - clockRatio) * (k * zMassSquared PMSubstrate.causalCoupling electronGeV) := by
  rw [mass_split]; ring

/-! ## Electron relation: the Yukawa fixed by the VEV -/

def closureYukawa : ℝ := Real.sqrt 2 / vevRatio PMSubstrate.causalCoupling

theorem closure_exact {me : ℝ} (hme : me ≠ 0) :
    closureYukawa * vev PMSubstrate.causalCoupling me / Real.sqrt 2 = me := by
  have hr : vevRatio PMSubstrate.causalCoupling ≠ 0 := (vev_ratio_bounds.1.trans' (by norm_num)).ne'
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  unfold closureYukawa vev; field_simp

def closureCoefficient : ℝ := (closureYukawa / bareYukawa - 1) / PMSubstrate.causalCoupling

theorem closure_ratio_bounds :
    (1.009397379 : ℝ) < closureYukawa / bareYukawa ∧ closureYukawa / bareYukawa < 1.0093973793 := by
  have hr := vev_ratio_bounds
  have hs := sqrt_two_bounds
  have hr0 : 0 < vevRatio PMSubstrate.causalCoupling := by linarith [hr.1]
  have heq : closureYukawa / bareYukawa = Real.sqrt 2 * 343914 / vevRatio PMSubstrate.causalCoupling := by
    unfold closureYukawa bareYukawa; field_simp; norm_num
  rw [heq]
  constructor
  · rw [lt_div_iff₀ hr0]; nlinarith [hr.1, hr.2, hs.1, hs.2]
  · rw [div_lt_iff₀ hr0]; nlinarith [hr.1, hr.2, hs.1, hs.2]

theorem closure_coefficient :
    (1.28777 : ℝ) < closureCoefficient ∧ closureCoefficient < 1.28779 := by
  have hq := closure_ratio_bounds
  have ha := alpha_bounds
  have ha0 : 0 < PMSubstrate.causalCoupling := by linarith [ha.1]
  unfold closureCoefficient
  constructor
  · rw [lt_div_iff₀ ha0]; nlinarith [hq.1, ha.2]
  · rw [div_lt_iff₀ ha0]; nlinarith [hq.2, ha.1]

theorem stated_dressing_excluded : closureCoefficient ≠ 5/4 := by
  have := closure_coefficient.1; intro h; rw [h] at this; norm_num at this

end PMConstants.ScaleConsistency
