import PMConstants.ElectroweakE8
import PMConstants.Allocation
import PMConstants.Hypercharge

/-! Certified geometric values inherited from Paper I. Decimal endpoints are
exact rationals. Matching these constants to physical observables is separate.
`constants_selected` states explicitly the allocation and representation premises.
-/

noncomputable section
namespace PMConstants.CertifiedConstants

abbrev α : ℝ := PMSubstrate.causalCoupling

theorem alpha_bounds :
    (0.007297352562 : ℝ) < α ∧ α < 0.007297352563 := by
  have hz : 0 < PMSubstrate.geometricIndex := by
    linarith [PMSubstrate.geometricIndex_gt_one]
  change (0.007297352562 : ℝ) < 1/PMSubstrate.geometricIndex ∧
    1/PMSubstrate.geometricIndex < 0.007297352563
  constructor
  · apply (lt_div_iff₀ hz).mpr
    nlinarith [PMSubstrate.geometricIndex_bounds.2]
  · apply (div_lt_iff₀ hz).mpr
    nlinarith [PMSubstrate.geometricIndex_bounds.1]

theorem strong_bounds :
    (0.1179031556 : ℝ) < strongCoupling α ∧ strongCoupling α < 0.1179031557 := by
  obtain ⟨hl, hu⟩ := alpha_bounds
  norm_num [strongCoupling, overhead]
  constructor <;> linarith

theorem weak_bounds :
    (0.2229053646 : ℝ) < clockRatio ∧ clockRatio < 0.2229053647 := by
  norm_num [clockRatio, footprint, overhead]

theorem scalar_bounds :
    (0.1294236602 : ℝ) < selfCoupling ∧ selfCoupling < 0.1294236603 := by
  norm_num [selfCoupling]

theorem electron_yukawa_bounds :
    (0.000002934226843 : ℝ) < ElectroweakE8.electronYukawa α ∧
      ElectroweakE8.electronYukawa α < 0.000002934226844 := by
  obtain ⟨hl, hu⟩ := alpha_bounds
  norm_num [ElectroweakE8.electronYukawa, ElectroweakE8.bareYukawa]
  constructor <;> linarith

/-- The proposed constants follow from the stated balance equations. The
fermion charges additionally require the specified invariant scalar couplings
and sterile neutrality. Persistence is not substituted for these hypotheses. -/
theorem constants_selected (v : Allocation.Values) (Y : Hypercharge.Charges)
    (halloc : Allocation.Compatible α v) (hflux : Hypercharge.Flux Y)
    (hyuk : Hypercharge.Yukawa Y 1) (hneutral : Y.n = 0) :
    v.η = overhead ∧ v.strong = strongCoupling α ∧ v.weak = clockRatio ∧
      v.scalar = selfCoupling ∧ Y = Hypercharge.standard := by
  obtain ⟨ho, hs, hw, hl⟩ := Allocation.allocation_forced α v halloc
  exact ⟨ho, hs, hw, hl, Hypercharge.charges_forced Y hflux hyuk hneutral⟩

end PMConstants.CertifiedConstants
