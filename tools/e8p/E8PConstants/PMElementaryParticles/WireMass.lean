import E8PConstants.Format
import PMConstants.Values

/-! The geometric Schur benchmark and the frozen charged-lepton references.

Two readings of `ReferenceNode`'s `α/2` exist, and the library settles which one the wire wants
(`PMAction.CarrierRateFromAdmittance`): the restoring crossing is pinned against an admittance,
the wire's row is in rates, and a probability fixes a pulse area rather than a rate.

* The **admittance reading** puts `α/2` straight into the rate slot: `m₂/m₃ ≈ 0.0045`, and no
  static insertion in `(0,1)` lifts it past `0.0073`. It is about `13` times below the measured
  `m_μ/m_τ`.
* The **rate reading** takes the common-duration area ratio `(2/π) arcsin √(α/2) ≈ 0.0385`:
  `m₂/m₃ ≈ 0.0471`. That removes a factor of ten and a half of the discrepancy, leaving about
  `26%`.
* `rate_reading_still_below` proves the rate reading is also below the frozen reference envelope,
  so the common-duration reading is excluded too, by `26%` rather than by an order of magnitude.

What the residual measures. With the areas fixed by `α`, the remaining freedom in
`CarrierRateFromAdmittance.rate_ratio` is the duration ratio `τ_certain / τ_restoring`, which is
the open quantity of `CertainTransferRate` (the duration of one carrier event). The measured ratio
inverts to a required duration ratio near `1.26`, reported below. A numerical scan of the static
insertion shows `m₂/m₃` falls with it, from `0.0471` at `s → 0` to `0.0411` at `s → 1`, so the
required duration ratio is a lower bound; that monotonicity is not proved, and only the `s → 0`
case is excluded in Lean.
-/
namespace E8PConstants.WireMass

open PMConstants.WireMassBounds

private def bareBounds : Rat × Rat := (0.0044, 0.0045)
private def shiftedUpper : Rat := 0.00730
private def rateBounds : Rat × Rat := (0.0470, 0.0472)

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

theorem rate_bounds_valid :
    (rateBounds.1 : ℝ) < Real.sqrt (3 * kRate ^ 2) / Real.sqrt (2 + kRate ^ 2) ∧
      Real.sqrt (3 * kRate ^ 2) / Real.sqrt (2 + kRate ^ 2) < (rateBounds.2 : ℝ) := by
  have h := rate_middle_heavy_bounds
  norm_num [rateBounds] at h ⊢
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

/-- **The rate reading is below the reference envelope as well.** So the common-duration reading
of `α/2` is excluded, not only the admittance reading. -/
theorem rate_reading_still_below :
    firstReferences.any (fun (muon, tau) =>
      decide (0 < tau.value - tau.uncertainty ∧
        rateBounds.2 < (referenceEnvelope muon tau).1)) = true := by decide +kernel

/-- The duration ratio the measured ratio requires, as an interval from the rate reading. -/
private def requiredDurationRatio (muon tau : ExpRef) : Rat × Rat :=
  ((referenceEnvelope muon tau).1 / rateBounds.2,
   (referenceEnvelope muon tau).2 / rateBounds.1)

def lines : List String :=
  ["Charged-lepton wire m_mu/m_tau (unscored Schur benchmark)",
   "  Normalization: common unit crossing, real resonance. Two readings of ReferenceNode's alpha/2.",
   "  Admittance reading (alpha/2 straight into the rate slot; a category error):",
   s!"    Bare (static offset = 0): {ratDecimal bareBounds.1 4} < m_2/m_3 < {ratDecimal bareBounds.2 4}.",
   s!"    Shifted (0 < static offset < 1): three positive modes, m_2/m_3 < {ratDecimal shiftedUpper 5}.",
   "  Rate reading ((2/pi) arcsin sqrt(alpha/2), common duration):",
   s!"    Bare: {ratDecimal rateBounds.1 4} < m_2/m_3 < {ratDecimal rateBounds.2 4}."] ++
  (match firstReferences with
   | none => ["  No frozen m_mu/m_tau reference pair."]
   | some (muon, tau) =>
     let center := muon.value / tau.value
     let (lo, hi) := referenceEnvelope muon tau
     let (dlo, dhi) := requiredDurationRatio muon tau
     [s!"  Frozen reference central ratio: {ratDecimal center 8} ({muon.citation}, {tau.citation}).",
      s!"  Reference endpoint envelope: [{fixedDecimal (lowerScaled lo 8) 8}, {fixedDecimal (upperScaled hi 8) 8}].",
      "  Both readings lie below the envelope, so both are excluded.",
      s!"  Required duration ratio tau_certain/tau_restoring: [{ratDecimal dlo 4}, {ratDecimal dhi 4}]."]) ++
  ["  That duration ratio is CertainTransferRate's open quantity: the duration of one carrier event.",
   "  The native rates and the full-wall mass spectrum are open."]

end E8PConstants.WireMass
