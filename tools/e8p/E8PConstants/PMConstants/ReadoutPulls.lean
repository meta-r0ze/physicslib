import E8PConstants.PMConstants.WeakMassPulls
import PMConstants.ReadoutAccounting
import PMConstants.GeneratorNormalization
import PMConstants.TableConsequences
import PMConstants.ContentWeight
import PMConstants.SharedReference
import PMConstants.ColourChannels
import PMConstants.GaugeTraceNormalization

/-!
# Readout-accounting measured pulls (moved from the PMConstants leaves)

The E8 selection (`ReadoutAccounting.selectedWeights`, `rawWMass`) and the
generator-normalization derivations (`GeneratorNormalization.mixing`, ...) stay in
`src`; the measured W-mass comparisons live here.

* `raw_w_window`: with the measured `m_Z`, the raw reading gives `84.22 < m_W < 84.24` GeV.
* `raw_excluded`: that is more than `289σ` above the direct world average `80.3692 ± 0.0133`.
* `ledgers_are_effective`: under the selected preparation, raw puts the W mass more than `289σ`
  off; effective puts it within `1.3σ`.
* `normalization_decided`: the trace-form normalization is excluded by more than `289σ`; charge
  units lie within `1.3σ`.
-/

noncomputable section
namespace E8PConstants.ReadoutPulls
open PMConstants GaugeLedgers RequirementComplement GaugeReadoutWeights RequirementTable ReferenceCharge

theorem raw_w_window {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    84.22 < ReadoutAccounting.rawWMass mZ ∧ ReadoutAccounting.rawWMass mZ < 84.24 := by
  have hs1 : (0.92366 : ℝ) < Real.sqrt (1 - 5547 / 37777) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt (1 - 5547 / 37777) < 0.92368 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold ReadoutAccounting.rawWMass
  constructor <;> nlinarith [h.1, h.2]

/-- **The raw reading is excluded** by the direct world average. -/
theorem raw_excluded {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    289 < WeakMassPulls.pull 80.3692 0.0133 (ReadoutAccounting.rawWMass mZ) := by
  have hw := raw_w_window h
  unfold WeakMassPulls.pull
  rw [lt_div_iff₀ (by norm_num)]; linarith

/-- **The ledgers are effective stiffness.** Under the selected preparation, reading them as raw
weights puts the W mass more than `289σ` off; reading them as effective puts it within `1.3σ`. -/
theorem ledgers_are_effective {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) {c : ℝ} (hc : 0 < c) :
    GaugeTraceNormalization.rawMixing c = 5547 / 37777 ∧
      289 < WeakMassPulls.pull 80.3692 0.0133 (ReadoutAccounting.rawWMass mZ) ∧
      WeakMassPulls.pull 80.3692 0.0133 (PMConstants.WMassTest.wMass mZ) < 1.3 ∧
      1.0 < WeakMassPulls.pull 80.3692 0.0133 (PMConstants.WMassTest.wMass mZ) :=
  ⟨GaugeTraceNormalization.raw_mixing_exact hc, raw_excluded h,
    (WeakMassPulls.pull_world h).2, (WeakMassPulls.pull_world h).1⟩

/-- **The W mass decides the normalization.** With the selected preparation and measured `m_Z`,
the trace-form normalization is excluded by more than `289σ`; charge units lie within `1.3σ`. -/
theorem normalization_decided {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) {c τ : ℝ}
    (hc : 0 < c) (hτ : 0 < τ) :
    GeneratorNormalization.mixing c 43 (footprint - 43) (2 / τ) ((10 / 3) / τ) = 5547 / 37777 ∧
      289 < WeakMassPulls.pull 80.3692 0.0133 (ReadoutAccounting.rawWMass mZ) ∧
      GeneratorNormalization.mixing c 43 (footprint - 43) 1 1 = clockRatio ∧
      WeakMassPulls.pull 80.3692 0.0133 (PMConstants.WMassTest.wMass mZ) < 1.3 :=
  ⟨(GeneratorNormalization.trace_form_gives_raw hc hτ).1, raw_excluded h,
    GeneratorNormalization.charge_units_give_effective hc, (WeakMassPulls.pull_world h).2⟩

/-- **The whole-phase W mass.** With `ρ = 1` (`ReferenceMasses.rho_one`),
`m_W = m_Z √(1 - s)` lies in `(80.3827, 80.38644)` GeV for the measured `m_Z`, within
`1.3σ` of the direct average. Moved here from `PMConstants.TableConsequences`. -/
theorem w_mass (_P : TableConsequences.Premises) {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    (80.3827 < mZ * Real.sqrt (1 - ledger reqSU2 / (ledger reqSU2 + ledger reqY)) ∧
      mZ * Real.sqrt (1 - ledger reqSU2 / (ledger reqSU2 + ledger reqY)) < 80.38644) ∧
      WeakMassPulls.pull 80.3692 0.0133 (PMConstants.WMassTest.wMass mZ) < 1.3 := by
  rw [mixing_from_rule]
  exact ⟨WeakMassPulls.w_window h, (WeakMassPulls.pull_world h).2⟩

/-- Squared-pull comparison of the two stored-content contracts, moved here from
`PMConstants.ContentWeight`. -/
theorem intensive_preferred {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    ContentWeight.chi 80.3692 0.0133 (PMConstants.WMassTest.wMass mZ) +
        ContentWeight.chi 0.1180 0.0009 (CertifiedConstants.α * footprint /
          ColourChannels.colourLedger) < 1.70 ∧
      2.5 < ContentWeight.chi 80.3692 0.0133
          (mZ * Real.sqrt (1 - 43 / ContentWeight.footprintW 1)) +
        ContentWeight.chi 0.1180 0.0009 (CertifiedConstants.α * ContentWeight.footprintW 1 /
          ContentWeight.colourW 1) := by
  have hw := WeakMassPulls.w_window h
  have hs := ColourChannels.strong_from_channels
  have ew := ContentWeight.extensive_w_mass h
  have es := ContentWeight.extensive_strong
  unfold ContentWeight.chi
  constructor
  · have a1 : ((PMConstants.WMassTest.wMass mZ - 80.3692) / 0.0133)^2 < 1.6901 := by
      rw [div_pow]; rw [div_lt_iff₀ (by norm_num)]; nlinarith [hw.1, hw.2]
    have a2 : ((CertifiedConstants.α * footprint / ColourChannels.colourLedger - 0.1180) / 0.0009)^2 < 0.0099 := by
      rw [div_pow]; rw [div_lt_iff₀ (by norm_num)]; nlinarith [hs.1, hs.2]
    linarith
  · have b1 : (2.04 : ℝ) < ((mZ * Real.sqrt (1 - 43 / ContentWeight.footprintW 1) - 80.3692) / 0.0133)^2 := by
      rw [div_pow]; rw [lt_div_iff₀ (by norm_num)]; nlinarith [ew.1, ew.2]
    have b2 : (0.49 : ℝ) < ((CertifiedConstants.α * ContentWeight.footprintW 1 / ContentWeight.colourW 1 - 0.1180) / 0.0009)^2 := by
      rw [div_pow]; rw [lt_div_iff₀ (by norm_num)]; nlinarith [es.1, es.2]
    linarith

/-- W mass for the quark-doublet reference, moved here from `PMConstants.SharedReference`. -/
theorem quark_w_window {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    48.1 < SharedReference.quarkWMass mZ ∧ SharedReference.quarkWMass mZ < 48.3 := by
  have hs1 : (0.5283 : ℝ) < Real.sqrt (1 - 16641 / 23087) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt (1 - 16641 / 23087) < 0.5285 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold SharedReference.quarkWMass
  constructor <;> nlinarith [h.1, h.2]

theorem quark_reference_excluded {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    ReferenceCharge.refMixing (weakIndex (ref .Q)) (hyperIndex (ref .Q)) = 16641 / 23087 ∧
      WeakMassPulls.pull 80.3692 0.0133 (SharedReference.quarkWMass mZ) < -2400 := by
  refine ⟨ReferenceCharge.quark_reference_mixing, ?_⟩
  have hw := quark_w_window h
  unfold WeakMassPulls.pull
  rw [div_lt_iff₀ (by norm_num)]; linarith

/-- Measured part of the shared-reference selection, moved here from `PMConstants.SharedReference`:
`Q` puts the W mass more than `2400σ` low; `L` gives the manuscript value within `1.3σ`. -/
theorem reference_selected_wmass (_L : SharedReference.ReferenceLayout)
    {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    WeakMassPulls.pull 80.3692 0.0133 (SharedReference.quarkWMass mZ) < -2400 ∧
      WeakMassPulls.pull 80.3692 0.0133 (PMConstants.WMassTest.wMass mZ) < 1.3 :=
  ⟨(quark_reference_excluded h).2, (WeakMassPulls.pull_world h).2⟩

end E8PConstants.ReadoutPulls
