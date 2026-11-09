import PMElementaryParticles.CompositeMasses
import PMSubstrate.E8Values

/-!

# Charged lepton and charged pion masses as E8 tier ledgers

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
* **Charged pion.** `2α⁻¹` (Coulomb self-energy of the two unit charges) − `χσ`
  (topological/symmetry product) + `1/(ν−χ)` (chiral leak) + `σ` + `D` −
  `α(σ−χ)/χ` (charge load).

**Status (A7).** The arithmetic is now purely E8-invariant and the feedback term
is *derived* as the fixed point of its recursive loop; the **assignment** of which
invariant pays which tier cost is the paper's proposed ledger — a declared model
input (`M`), not a cost-selected choice (there is no option family/cost
functional over tier ledgers yet). The measured CODATA/PDG comparisons live in
`tools/e8p/E8PConstants/LeptonMassPulls.lean`.
-/

noncomputable section
namespace PMElementaryParticles.LeptonMasses
open PMElementaryParticles.CompositeMasses
open PMSubstrate.E8Values

/-! ## Tier ledgers -/

/-- Muon (Tier 1, line): sweep through the internal symmetry. -/
def muonSweep : ℝ := (Delta : ℝ) * (sigma : ℝ)
/-- Muon: topological anchor. -/
def muonAnchor : ℝ := (chi : ℝ)
/-- Muon: double-cover spin phase lag. -/
def muonSpinLag : ℝ := 2 * Real.pi
/-- Muon: vacuum feedback load `(χ+σ)·α/(1−α)`. -/
def muonFeedback : ℝ := ((chi + sigma : ℕ) : ℝ) * αe / (1 - αe)

/-- Muon mass in `m_e` units. -/
def muon : ℝ := muonSweep - muonAnchor - muonSpinLag + muonFeedback

/-- The muon is exactly the sum of its named tier costs. -/
theorem muon_ledger :
    muon = (Delta : ℝ) * (sigma : ℝ) - (chi : ℝ) - 2 * Real.pi +
      ((chi + sigma : ℕ) : ℝ) * αe / (1 - αe) := by
  unfold muon muonSweep muonAnchor muonSpinLag muonFeedback; ring

/-- **The feedback load is the recursive loop's fixed point.** The total load of the
admittance ladder `x = (χ+σ)α + α·x` is `(χ+σ)α/(1−α)`. -/
theorem muonFeedback_fixpoint (hα : αe ≠ 1) :
    muonFeedback = ((chi + sigma : ℕ) : ℝ) * αe + αe * muonFeedback := by
  have h : 1 - αe ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  unfold muonFeedback
  field_simp
  ring

/-- Tau (Tier 2, area): boundary cost over the causal area. -/
def tauBoundary : ℝ := (chi : ℝ) * (Delta : ℝ) ^ 2
/-- Tau: inherited linear core latency. -/
def tauCoreLatency : ℝ := (sigma : ℝ) * (Delta : ℝ)
/-- Tau: spacetime anchors. -/
def tauAnchors : ℝ := (D : ℝ) + (chi : ℝ)

/-- Tau mass in `m_e` units. -/
def tau : ℝ := tauBoundary - tauCoreLatency - tauAnchors

/-- The tau is exactly the sum of its named tier costs. -/
theorem tau_ledger :
    tau = (chi : ℝ) * (Delta : ℝ) ^ 2 - (sigma : ℝ) * (Delta : ℝ) -
      ((D : ℝ) + (chi : ℝ)) := by
  unfold tau tauBoundary tauCoreLatency tauAnchors; ring

/-- Pion: Coulomb self-energy of the two unit charges. -/
def pionCoulomb : ℝ := 2 * αinv
/-- Pion: topological/symmetry product. -/
def pionTopological : ℝ := (chi : ℝ) * (sigma : ℝ)
/-- Pion: chiral leak `1/(ν−χ)`. -/
def pionLeak : ℝ := 1 / ((nu : ℝ) - (chi : ℝ))
/-- Pion: internal symmetry weight. -/
def pionSymmetry : ℝ := (sigma : ℝ)
/-- Pion: spacetime anchor. -/
def pionAnchor : ℝ := (D : ℝ)
/-- Pion: charge load `α(σ−χ)/χ`. -/
def pionChargeLoad : ℝ := αe * (((sigma : ℝ) - (chi : ℝ)) / (chi : ℝ))

/-- Charged-pion mass in `m_e` units. -/
def pionPlus : ℝ :=
  pionCoulomb - pionTopological + pionLeak + pionSymmetry + pionAnchor - pionChargeLoad

/-- The pion is exactly the sum of its named costs. -/
theorem pionPlus_ledger :
    pionPlus = 2 * αinv - (chi : ℝ) * (sigma : ℝ) + 1 / ((nu : ℝ) - (chi : ℝ)) +
      (sigma : ℝ) + (D : ℝ) - αe * (((sigma : ℝ) - (chi : ℝ)) / (chi : ℝ)) := by
  unfold pionPlus pionCoulomb pionTopological pionLeak pionSymmetry pionAnchor pionChargeLoad
  ring

/-! ## E8-only enclosures -/

theorem muon_value : 206.7682716 < muon ∧ muon < 206.7682718 := by
  have hp := pi_b; have ha := a_b
  have h1 : 0 < 1 - αe := by linarith [ha.2]
  have q1 : αe * 7 / (1 - αe) < 0.05145697 := by
    rw [div_lt_iff₀ h1]; nlinarith [ha.1, ha.2]
  have q2 : 0.05145696 < αe * 7 / (1 - αe) := by
    rw [lt_div_iff₀ h1]; nlinarith [ha.1, ha.2]
  have hm : muon = 215 - 2 - 2 * Real.pi + αe * 7 / (1 - αe) := by
    rw [muon_ledger]
    rw [PMSubstrate.E8Values.Delta_eq, PMSubstrate.E8Values.sigma_eq,
      PMSubstrate.E8Values.chi_eq]
    norm_num
    ring
  rw [hm]; constructor <;> nlinarith [hp.1, hp.2]

theorem tau_value : tau = 3477 := by
  rw [tau_ledger]
  rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.D_eq]
  norm_num

/-- A direct two-sided enclosure of the charged pion in `m_e` units. -/
theorem pionPlus_value : (273.1 : ℝ) < pionPlus ∧ pionPlus < 273.2 := by
  have hg := g_b; have ha := a_b
  rw [pionPlus_ledger]
  rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.D_eq]
  constructor <;> nlinarith [hg.1, hg.2, ha.1, ha.2]

/-- The charged-pion mass in MeV, as an E8-only enclosure (no measured reference). -/
theorem pionPlus_mev_value : (139.570354 : ℝ) < pionPlus * me ∧ pionPlus * me < 139.570426 := by
  have hg := g_b; have ha := a_b
  rw [pionPlus_ledger]
  rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.D_eq]
  unfold me
  constructor <;> nlinarith [hg.1, hg.2, ha.1, ha.2]

end PMElementaryParticles.LeptonMasses
