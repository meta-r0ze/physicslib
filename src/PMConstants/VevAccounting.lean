import PMConstants.ElectroweakBounds
import PMConstants.ContentWeight

/-!
# Which subtraction the VEV formula can persist with

The proposed VEV is `v = (χΔ² − L) α⁻¹ m_e (1 + α/D_eff)(1 − PM/3)` with `L = DΔ + ν = 188`.
Earlier modules fixed how the footprint is counted: the address frame has unit weight, stored
payload content weighs `η` (`ContentWeight.economy_selects_intensive`), and the per-phase
footprint is `N_sys = 172 + 16η + 5`. The measured Fermi constant fixes `v_F = (√2G_F)^{-1/2}` to
about `2.6·10⁻⁷`, far finer than any of these choices, so it decides which subtraction persists.

* `fermi_window`: for `G_F` in `(1.1663782, 1.1663794)·10⁻⁵ GeV⁻²`, `246.21957 < v_F < 246.21971`.
* `frame_inside`: with `L = 188` (the 172 addresses and the 16 channels, both frame, unit
  weight) the formula lies inside the window.
* `payload_outside`: counting the 16 as stored payload, `L = 172 + 16η`, raises `v` by the exact
  factor `1 + (4/43)/3510` and puts it above `246.2261`, outside the window.
* `footprint_outside`: subtracting the whole footprint, `L = N_sys`, puts it below `245.876`.

So the VEV formula persists only if its `ν` counts channels as frame, not their payload content,
and only if the wires `σ` are not subtracted. Those two readings are the remaining premises of the
formula's slot count; the factor `α⁻¹` and the two corrections are separate premises.
-/

noncomputable section
namespace PMConstants.VevAccounting
open PMConstants Electroweak CertifiedConstants ElectroweakBounds

theorem fermi_window {GF : ℝ} (h : 1.1663782e-5 < GF ∧ GF < 1.1663794e-5) :
    246.21957 < Real.sqrt (1 / (Real.sqrt 2 * GF)) ∧
      Real.sqrt (1 / (Real.sqrt 2 * GF)) < 246.21971 := by
  have hs := JointConstants.sqrt_two_bounds
  have hd : 0 < Real.sqrt 2 * GF := by nlinarith [hs.1, h.1]
  constructor
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ hd]; nlinarith [hs.2, h.2]
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ hd]; nlinarith [hs.1, h.1]

/-- The formula with a general subtraction `L`. -/
def vevWith (L : ℝ) : ℝ := vev α electronGeV * ((2 * 43^2 - L) / 3510)

theorem frame_is_paper : vevWith 188 = vev α electronGeV := by
  unfold vevWith; norm_num

theorem frame_inside {GF : ℝ} (h : 1.1663782e-5 < GF ∧ GF < 1.1663794e-5) :
    Real.sqrt (1 / (Real.sqrt 2 * GF)) - 0.00008 < vevWith 188 ∧
      vevWith 188 < Real.sqrt (1 / (Real.sqrt 2 * GF)) + 0.00008 := by
  have hw := fermi_window h
  have hv := vev_bounds
  rw [frame_is_paper]
  constructor <;> linarith [hw.1, hw.2, hv.1, hv.2]

theorem payload_outside {GF : ℝ} (h : 1.1663782e-5 < GF ∧ GF < 1.1663794e-5) :
    Real.sqrt (1 / (Real.sqrt 2 * GF)) < 246.2261 ∧ 246.2261 < vevWith (172 + 16 * overhead) := by
  have hw := fermi_window h
  have hv := vev_bounds
  refine ⟨by linarith [hw.2], ?_⟩
  unfold vevWith; norm_num [overhead]
  nlinarith [hv.1]

theorem footprint_outside {GF : ℝ} (h : 1.1663782e-5 < GF ∧ GF < 1.1663794e-5) :
    vevWith footprint < 245.876 ∧ 245.876 < Real.sqrt (1 / (Real.sqrt 2 * GF)) := by
  have hw := fermi_window h
  have hv := vev_bounds
  refine ⟨?_, by linarith [hw.1]⟩
  unfold vevWith; norm_num [footprint, overhead]
  nlinarith [hv.2]

end PMConstants.VevAccounting
