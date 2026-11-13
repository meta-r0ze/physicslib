import PMElementaryParticles.SharedUnits
import PMConstants.StrongRunning

/-!

# Paper V's quark mass formulas as named E8 tier ledgers

Units of `m_e`, `η = 171/172`. Every numeral is the canonical `PMSubstrate.E8Values`
invariant (`Δ = 43`, `ν = 16`, `σ = 5`, `χ = 2`, `D = 4`), so no measured literal
appears in a mass formula.

The paper (`PM-5 §Protocol ledger`) reads each quark as a tier `Δⁿ` of a protocol
paying named geometric costs; `anchorPoint`, `anchorLine`, `anchorArea`,
`anchorVolume` are the `DΔⁿ` anchors, and the drag/leak components are the
corrections:

| Tier | Formula | Named costs |
| --- | --- | --- |
| up (P2, point) | `D/η` | anchor `D` |
| down (P3, point) | `(D+σ)/η` | anchor `D` + symmetry `σ` |
| strange (P3, line) | `(DΔ + χσ)/η` | anchor `DΔ` + drag `χσ = 2σ` |
| charm (P2, area) | `DΔ²/(η(σ−χ))` | anchor `DΔ²` diluted by `σ−χ = 3` |
| bottom (P3, area) | `Δ²(D + χ/σ)/η` | anchor `DΔ²` + latency leak `Δ²χ/σ` |
| top (P2, volume) | `Δ³(D + 1/D)` | anchor `DΔ³` + capacity leak `Δ³/D` |

**Status (A7).** The arithmetic is E8-invariant and each term is named with the
paper's reading (`up_ledger` … `top_ledger`). The **assignment** of which invariant
pays which tier cost is the paper's proposed protocol ledger — a declared model
input (`M`), not cost-selected (there is no option family/cost functional over
tier ledgers). The measured PDG 2024 pulls live in
`tools/e8p/E8PConstants/PMElementaryParticles/QuarkMassPulls.lean`.

These are the formulas Paper III's `StrongRunning` uses for the flavour thresholds
(`m_c`, `m_b`, `threshold_match`).
-/

noncomputable section
namespace PMElementaryParticles.QuarkMasses
open PMElementaryParticles.SharedUnits
open PMSubstrate.E8Values

/-- Per-cell overhead `η = 171/172`. -/
def η : ℝ := overhead

/-! ## Masses -/

def up : ℝ := (D : ℝ) / η
def down : ℝ := ((D : ℝ) + (sigma : ℝ)) / η
def strange : ℝ := ((D : ℝ) * (Delta : ℝ) + (chi : ℝ) * (sigma : ℝ)) / η
def charm : ℝ := (D : ℝ) * (Delta : ℝ) ^ 2 / (η * ((sigma : ℝ) - (chi : ℝ)))
def bottom : ℝ := (Delta : ℝ) ^ 2 * ((D : ℝ) + (chi : ℝ) / (sigma : ℝ)) / η
def top : ℝ := (Delta : ℝ) ^ 3 * ((D : ℝ) + 1 / (D : ℝ))

/-! ## Named tier costs (the paper's protocol ledger) -/

/-- Point anchor `D`. -/
def anchorPoint : ℝ := (D : ℝ)
/-- Internal-symmetry weight `σ`. -/
def symWeight : ℝ := (sigma : ℝ)
/-- Linear anchor `DΔ`. -/
def anchorLine : ℝ := (D : ℝ) * (Delta : ℝ)
/-- Additive double-symmetry drag `χσ = 2σ`. -/
def dragSym : ℝ := (chi : ℝ) * (sigma : ℝ)
/-- Areal anchor `DΔ²`. -/
def anchorArea : ℝ := (D : ℝ) * (Delta : ℝ) ^ 2
/-- Colour dilution `σ − χ`. -/
def colourDim : ℝ := (sigma : ℝ) - (chi : ℝ)
/-- Boundary-to-symmetry latency ratio `χ/σ`. -/
def latencyRatio : ℝ := (chi : ℝ) / (sigma : ℝ)
/-- Areal latency leak `Δ²χ/σ`. -/
def latencyTerm : ℝ := (Delta : ℝ) ^ 2 * latencyRatio
/-- Volumetric anchor `DΔ³`. -/
def anchorVolume : ℝ := (D : ℝ) * (Delta : ℝ) ^ 3
/-- Reciprocal capacity leak `1/D`. -/
def capLeak : ℝ := 1 / (D : ℝ)
/-- Volumetric capacity leak `Δ³/D`. -/
def capLeakTerm : ℝ := (Delta : ℝ) ^ 3 * capLeak

/-- The up quark is anchored to the spacetime manifold alone. -/
theorem up_ledger : up = anchorPoint / η := by unfold up anchorPoint; ring

/-- The down quark carries the manifold anchor plus the internal symmetry weight. -/
theorem down_ledger : down = (anchorPoint + symWeight) / η := by
  unfold down anchorPoint symWeight; ring

/-- The strange quark is a linear anchor plus the additive double-symmetry drag
`χσ = 2σ`. -/
theorem strange_ledger : strange = (anchorLine + dragSym) / η := by
  unfold strange anchorLine dragSym; ring

/-- The charm quark is an areal anchor diluted by the `σ − χ` colour dimensions. -/
theorem charm_ledger : charm = anchorArea / (η * colourDim) := by
  unfold charm anchorArea colourDim; ring

/-- The bottom quark is an areal anchor plus the boundary-to-symmetry latency leak. -/
theorem bottom_ledger : bottom = (anchorArea + latencyTerm) / η := by
  unfold bottom anchorArea latencyTerm latencyRatio; ring

/-- The top quark is a volumetric anchor plus the reciprocal capacity leak
`Δ³/D`. -/
theorem top_ledger : top = anchorVolume + capLeakTerm := by
  unfold top anchorVolume capLeakTerm capLeak; ring

/-! ## E8-only enclosures (no measured reference) -/

/-- E8-only enclosure of the up-quark mass, matching the `e8p` catalog interval. -/
theorem up_value : (2.055 : ℝ) < up * me ∧ up * me < (2.062 : ℝ) := by
  unfold up η
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.overhead_eq]
  norm_num [me, PMSubstrate.SIUnits.electronMassMeV]

/-- E8-only enclosure of the down-quark mass. -/
theorem down_value : (4.623 : ℝ) < down * me ∧ down * me < (4.63 : ℝ) := by
  unfold down η
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.overhead_eq]
  norm_num [me, PMSubstrate.SIUnits.electronMassMeV]

/-- E8-only enclosure of the strange-quark mass. -/
theorem strange_value : (93.5 : ℝ) < strange * me ∧ strange * me < (93.58 : ℝ) := by
  unfold strange η
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.overhead_eq]
  norm_num [me, PMSubstrate.SIUnits.electronMassMeV]

/-- E8-only enclosure of the charm-quark mass. -/
theorem charm_value : (1267.02 : ℝ) < charm * me ∧ charm * me < (1267.48 : ℝ) := by
  unfold charm η
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.overhead_eq]
  norm_num [me, PMSubstrate.SIUnits.electronMassMeV]

/-- E8-only enclosure of the bottom-quark mass. -/
theorem bottom_value : (4180.9 : ℝ) < bottom * me ∧ bottom * me < (4182.3 : ℝ) := by
  unfold bottom η
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.overhead_eq]
  norm_num [me, PMSubstrate.SIUnits.electronMassMeV]

/-- E8-only enclosure of the top-quark mass. -/
theorem top_value : (172657 : ℝ) < top * me ∧ top * me < (172686 : ℝ) := by
  unfold top
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq]
  norm_num [me, PMSubstrate.SIUnits.electronMassMeV]

/-- The thresholds Paper III orders are these formulas. -/
theorem threshold_match : charm = PMConstants.StrongRunning.mCharm ∧ bottom = PMConstants.StrongRunning.mBottom := by
  unfold charm bottom η PMConstants.StrongRunning.mCharm PMConstants.StrongRunning.mBottom PMConstants.overhead
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq,
    PMSubstrate.E8Values.overhead_eq]
  constructor <;> ring

end PMElementaryParticles.QuarkMasses
