import PMConstants.StrongLedgerBounds
import PMConstants.CertifiedConstants

/-! Public snapshot of the current manuscript formulas. The old dressed Yukawa
and old strong formula remain available as regression/exclusion results; they
are not the current predictions. These are conditional model consequences,
not a proof that PM's basic postulates select the input formulas. -/
noncomputable section
namespace PMConstants.CurrentConstants
open PMConstants

abbrev alpha : ℝ := CertifiedConstants.α
abbrev strong : ℝ := StrongLedgerBounds.ledgerStrong
abbrev weakFraction : ℝ := clockRatio
abbrev scalar : ℝ := selfCoupling
abbrev electronYukawa : ℝ := ScaleConsistency.closureYukawa

theorem strong_bounds : (0.11799520370 : ℝ) < strong ∧ strong < 0.11799520373 := by
  have ha := CertifiedConstants.alpha_bounds
  have he : strong=alpha*(2765/171) := by
    norm_num [strong,StrongLedgerBounds.ledgerStrong,ColourChannels.colourLedger,footprint,overhead]
    ring
  rw [he]
  constructor <;> nlinarith [ha.1,ha.2]

theorem electron_bounds : (0.00000293502845 : ℝ) < electronYukawa ∧
    electronYukawa < 0.00000293502847 := by
  have hv := JointConstants.vev_ratio_bounds
  have hs := JointConstants.sqrt_two_bounds
  have hp : 0 < Electroweak.vevRatio alpha := by linarith [hv.1]
  change _ < Real.sqrt 2/Electroweak.vevRatio alpha ∧
    Real.sqrt 2/Electroweak.vevRatio alpha < _
  constructor
  · apply (lt_div_iff₀ hp).mpr; nlinarith [hv.2,hs.1]
  · apply (div_lt_iff₀ hp).mpr; nlinarith [hv.1,hs.2]

/-- A single checked entry point for the manuscript's current dimensionless
values and its exact, VEV-defined electron mass closure. -/
theorem current_snapshot :
    (0.007297352562 < alpha ∧ alpha < 0.007297352563) ∧
    (0.11799520370 < strong ∧ strong < 0.11799520373) ∧
    weakFraction=1849/8295 ∧ scalar=128/989 ∧
    (∀ me : ℝ, me ≠ 0 → electronYukawa*Electroweak.vev alpha me/Real.sqrt 2=me) := by
  refine ⟨CertifiedConstants.alpha_bounds, strong_bounds, ?_, ?_, ?_⟩
  · norm_num [weakFraction,clockRatio,footprint,overhead]
  · norm_num [scalar,selfCoupling]
  · intro me hme; exact ScaleConsistency.closure_exact hme

/-- These two legacy formulas genuinely differ from the current public values. -/
theorem legacy_distinct :
    strong ≠ strongCoupling alpha ∧ electronYukawa ≠ Electroweak.electronYukawa alpha := by
  constructor
  · intro h
    have hl := ColourChannels.strong_from_channels.1
    have hu := CertifiedConstants.strong_bounds.2
    change (0.11799 : ℝ) < strong at hl
    rw [h] at hl
    linarith
  · intro h
    have hc := ScaleConsistency.closure_exact (me := (1 : ℝ)) (by norm_num)
    change electronYukawa*Electroweak.vev alpha 1/Real.sqrt 2=1 at hc
    rw [h] at hc
    exact JointConstants.no_exact_electron_closure (by norm_num : (1 : ℝ) ≠ 0) hc

end PMConstants.CurrentConstants
