import PMConstants.PersistentGain
import PMConstants.JointConstants

/-!
# The scalar sector against data without the predicted VEV

Paper III's scalar quantities split into a gain `λ` and a scale `v`. The event-law chain
(`EventStiffness`, `LinkFromEvents`) fixes the gauge side and the W/Z mass form but not the
overall scale, so the cleanest test of the scalar sector is one in which `v` cancels.

* `lambda_insensitive`: the persistent gain `g*` of `PersistentGain` depends on the unknown
  reflection charge rate `c`, but for every `0 < c ≤ 10⁴` it lies within `4.4·10⁻⁶` of
  `λ = 128/989`, fifty times below the present resolution of `λ`. Deriving `c` cannot move
  any comparison, so it is not needed.
* `higgs_from_fermi`: the measured Fermi constant fixes `v_F² = 1/(√2 G_F)`. With the paper's `λ`,
  `m_H = √(2λ) v_F` lies in `(125.26, 125.28)` GeV for `G_F` in `(1.1663782, 1.1663794)·10⁻⁵ GeV⁻²`.
  This uses neither the proposed VEV formula nor the electron mass.
* `higgs_pull`: against `m_H = 125.20 ± 0.11` GeV (PDG 2024) the pull lies in `(0.5, 0.75)`.

So `λ = 128/989` passes a test independent of the VEV derivation. The VEV formula itself,
`v = (χΔ² − L)α⁻¹m_e(1 ± corrections)`, remains outside the event-law chain and was found not
significant by the look-elsewhere check; the scale is the open part of the scalar sector.
-/

noncomputable section
namespace PMConstants.ScalarSector
open PMConstants PersistentGain

theorem lambda_insensitive {c : ℝ} (hc : 0 < c) (hc' : c ≤ 10000) :
    ∃ gs, Persistent c gs ∧ (∀ g, Persistent c g → g ≤ gs) ∧ gs < selfCoupling ∧
      selfCoupling - gs < 0.0000044 := by
  obtain ⟨gs, hp, hmax, -, hlt, hd⟩ := persistent_maximum hc
  refine ⟨gs, hp, hmax, hlt, ?_⟩
  have : c * 0.00000001 / 23 ≤ 10000 * 0.00000001 / 23 := by
    apply div_le_div_of_nonneg_right _ (by norm_num); nlinarith
  linarith [show (10000 : ℝ) * 0.00000001 / 23 < 0.0000044 by norm_num]

/-- `m_H² = 2λ v_F²` with `v_F² = 1/(√2 G_F)`. -/
def higgsSq (GF : ℝ) : ℝ := 2 * selfCoupling / (Real.sqrt 2 * GF)

theorem higgs_from_fermi {GF : ℝ} (h : 1.1663782e-5 < GF ∧ GF < 1.1663794e-5) :
    125.26 < Real.sqrt (higgsSq GF) ∧ Real.sqrt (higgsSq GF) < 125.28 := by
  have hs := JointConstants.sqrt_two_bounds
  have hd : 0 < Real.sqrt 2 * GF := by nlinarith [hs.1, h.1]
  have hlo : (125.26 : ℝ)^2 < higgsSq GF := by
    unfold higgsSq selfCoupling
    rw [PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.sigma_eq,
      PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.Delta_eq]
    rw [lt_div_iff₀ hd]; nlinarith [hs.2, h.2]
  have hhi : higgsSq GF < (125.28 : ℝ)^2 := by
    unfold higgsSq selfCoupling
    rw [PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.sigma_eq,
      PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.Delta_eq]
    rw [div_lt_iff₀ hd]; nlinarith [hs.1, h.1]
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; exact hlo
  · rw [Real.sqrt_lt' (by norm_num)]; exact hhi

theorem higgs_pull {GF : ℝ} (h : 1.1663782e-5 < GF ∧ GF < 1.1663794e-5) :
    0.5 < (Real.sqrt (higgsSq GF) - 125.20) / 0.11 ∧ (Real.sqrt (higgsSq GF) - 125.20) / 0.11 < 0.75 := by
  have hm := higgs_from_fermi h
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

end PMConstants.ScalarSector
