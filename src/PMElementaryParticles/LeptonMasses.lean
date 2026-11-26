import PMSubstrate.SpeciesFootprints
import PMElementaryParticles.SharedUnits

/-!

# Charged lepton masses as E8 tier ledgers

Units of `m_e`; `α`, `α⁻¹`, `π` as in `CompositeMasses`. Every numeral is the
canonical `PMSubstrate.E8Values` invariant (`Δ = 43`, `ν = 16`, `σ = 5`,
`χ = 2`, `D = 4`), so no measured literal appears in a mass formula.

The paper (`PM-5 §Protocol ledger`) reads each charged lepton as a resonant tier
`Δⁿ` paying **named** geometric costs:

* **Muon (Tier 1, line).** `Δσ` (sweep through the internal symmetry) − `χ`
  (topological anchor) − `2π` (double-cover spin phase lag) + the vacuum feedback
  `(χ + σ)·Σ_{n≥1} αⁿ`. `muon_ledger` records the decomposition and
  `muonFeedback_fixpoint` shows the feedback is the fixed point of the recursive
  loop `x = (χ+σ)α + α·x`, i.e. the total load of the infinite geometric ladder,
  not a fitted add-on.
* **Tau (Tier 2, area).** `χΔ²` (boundary cost over the causal area) − `σΔ`
  (inherited linear core latency) − `(D + χ)` (spacetime anchors).

The charged pion is a hadron; its tier ledger is in `PMHadrons.MesonMasses`.

**Legacy audit status.** This is a declared legacy ledger: the E8 arithmetic and
the feedback fixed point are certified, but the tier assignment is not derived
by the persistence rebuild. It remains a premise, not contradicted.

**Status (A7).** The arithmetic is now purely E8-invariant and the feedback term
is *derived* as the fixed point of its recursive loop; the **assignment** of which
invariant pays which tier cost is the paper's proposed ledger — a declared model
input (`M`), not a cost-selected choice (there is no option family/cost
functional over tier ledgers yet). The measured CODATA/PDG comparisons live in
`tools/e8p/E8PConstants/PMElementaryParticles/LeptonMassPulls.lean`.

## Feedback and pillar checks

The feedback fixed point is certified for the supplied muon loop.
No theorem derives the choice of that loop, the tau residual, or a common pillar sign rule.
The measured residual audit is in the reporter's `LeptonMassPulls` docstring.
-/

noncomputable section
namespace PMElementaryParticles.LeptonMasses
open PMElementaryParticles.SharedUnits PMSubstrate.E8Values

export PMSubstrate.SpeciesFootprints.Lepton
  (muonSweep muonAnchor muonSpinLag muonFeedback muonFootprint muon muon_ledger
  muonFeedback_fixpoint tauBoundary tauCoreLatency tauAnchors tauFootprint tau tau_ledger)

/-! ## E8-only enclosures -/

theorem muon_value : 206.7682716 < muon ∧ muon < 206.7682718 := by
  have hp := pi_b; have ha := a_b
  have h1 : 0 < 1 - PMConstants.Values.alpha := by linarith [ha.2]
  have q1 : PMConstants.Values.alpha * 7 / (1 - PMConstants.Values.alpha) < 0.05145697 := by
    rw [div_lt_iff₀ h1]; nlinarith [ha.1, ha.2]
  have q2 : 0.05145696 < PMConstants.Values.alpha * 7 / (1 - PMConstants.Values.alpha) := by
    rw [lt_div_iff₀ h1]; nlinarith [ha.1, ha.2]
  have hm : muon = 215 - 2 - 2 * Real.pi + PMConstants.Values.alpha * 7 / (1 - PMConstants.Values.alpha) := by
    rw [muon_ledger]
    rw [PMSubstrate.E8Values.Delta_eq, PMSubstrate.E8Values.sigma_eq,
      PMSubstrate.E8Values.chi_eq]
    norm_num
    rw [show PMConstants.Values.alpha = PMSubstrate.causalCoupling from rfl]
    ring
  rw [hm]; constructor <;> nlinarith [hp.1, hp.2]

theorem tau_value : tau = 3477 := by
  rw [tau_ledger]
  rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.D_eq]
  norm_num

end PMElementaryParticles.LeptonMasses
