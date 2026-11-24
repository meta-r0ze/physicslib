import E8PConstants.Format
import PMConstants.WireMassBounds

/-! The geometric Schur benchmark and the frozen charged-lepton references. -/
namespace E8PConstants.WireMass

open PMConstants.WireMassBounds

private def bareBounds : Rat × Rat := (0.0044, 0.0045)
private def shiftedUpper : Rat := 0.00730

theorem bare_bounds_valid :
    let k := PMConstants.CertifiedConstants.α / 2
    let ratio := Real.sqrt (3 * k ^ 2) / Real.sqrt (2 + k ^ 2)
    (bareBounds.1 : ℝ) < ratio ∧ ratio < (bareBounds.2 : ℝ) := by
  have h := bare_middle_heavy_bounds
  norm_num [bareBounds] at h ⊢
  exact h

theorem shifted_upper_valid (s : ℝ) (hs : 0 < s) (hs₁ : s < 1) :
    let k := PMConstants.CertifiedConstants.α / 2
    ∃ m₁ m₂ m₃ : ℝ, 0 < m₁ ∧ m₁ < m₂ ∧ m₂ < m₃ ∧ m₂ / m₃ < (shiftedUpper : ℝ) ∧
      ∀ m : ℝ, 0 ≤ m →
        (m ^ 2 ∈ spectrum ℝ (PMAction.WireResonanceSpectrum.gram k s) ↔
          m = m₁ ∨ m = m₂ ∨ m = m₃) := by
  have h := shifted_middle_heavy_bound s hs hs₁
  norm_num [shiftedUpper] at h ⊢
  exact h

/-- Monotone quotient bounds built from the two positive reference intervals.
This is an endpoint envelope for the stated inputs, with no covariance model. -/
private def referenceEnvelope (muon tau : ExpRef) : Rat × Rat :=
  ((muon.value - muon.uncertainty) / (tau.value + tau.uncertainty),
   (muon.value + muon.uncertainty) / (tau.value - tau.uncertainty))

private def firstReferences : Option (ExpRef × ExpRef) := do
  let muon ← (expRefs .muonRatio).head?
  let tau ← (expRefs .tauRatio).head?
  return (muon, tau)

/-- Both reported Schur cases fall below the frozen reference envelope. -/
theorem reference_separation :
    firstReferences.any (fun (muon, tau) =>
      decide (0 < tau.value - tau.uncertainty ∧
        bareBounds.2 < (referenceEnvelope muon tau).1 ∧
        shiftedUpper < (referenceEnvelope muon tau).1)) = true := by decide +kernel

def lines : List String :=
  ["Charged-lepton wire m_mu/m_tau (unscored Schur benchmark)",
   "  Normalization: common unit crossing, real resonance, k = alpha/2 as a rate premise.",
   s!"  Bare (static offset = 0): {ratDecimal bareBounds.1 4} < m_2/m_3 < {ratDecimal bareBounds.2 4}.",
   s!"  Shifted (0 < static offset < 1): three positive modes, m_2/m_3 < {ratDecimal shiftedUpper 5}."] ++
  (match firstReferences with
   | none => ["  No frozen m_mu/m_tau reference pair."]
   | some (muon, tau) =>
     let center := muon.value / tau.value
     let (lo, hi) := referenceEnvelope muon tau
     [s!"  Frozen reference central ratio: {ratDecimal center 8} ({muon.citation}, {tau.citation}).",
      s!"  Reference endpoint envelope: [{fixedDecimal (lowerScaled lo 8) 8}, {fixedDecimal (upperScaled hi 8) 8}]."]) ++
  ["  The native rates and the full-wall mass spectrum are open."]

end E8PConstants.WireMass
