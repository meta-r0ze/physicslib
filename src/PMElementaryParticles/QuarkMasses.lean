import PMSubstrate.OccupancyCost
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

**Legacy audit status.** This is a declared legacy ledger: the E8 arithmetic is
certified, but the assignment of quark formulas to tiers is not derived by the
persistence rebuild (`Protocol`, `RecordPortIdentification`, `PhaseToRecord`).
It remains a premise, not contradicted.

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
open PMSubstrate.E8Values PMSubstrate.OccupancyCost

/-- Per-cell overhead `η = 171/172`. -/
def η : ℝ := overhead

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

/-! The spacetime anchors use the Capacity price units. These declared
counts preserve the old ledger. Selection of the clock region and of the
multipliers is open. -/

def upFootprint : Footprint :=
  { capacity := capacityCount (anchorPoint / η) }

def downFootprint : Footprint :=
  { capacity := capacityCount (anchorPoint / η)
    protocol := protocolCount (symWeight / η) }

def strangeFootprint : Footprint :=
  { capacity := capacityCount (anchorLine / η)
    protocol := protocolCount (dragSym / η) }

def charmFootprint : Footprint :=
  { capacity := capacityCount (anchorArea / (η * colourDim)) }

def bottomFootprint : Footprint :=
  { capacity := capacityCount (anchorArea / η)
    residual := latencyTerm / η }

def topFootprint : Footprint :=
  { capacity := capacityCount (anchorVolume + capLeakTerm) }

abbrev up : ℝ := cost upFootprint
abbrev down : ℝ := cost downFootprint
abbrev strange : ℝ := cost strangeFootprint
abbrev charm : ℝ := cost charmFootprint
abbrev bottom : ℝ := cost bottomFootprint
abbrev top : ℝ := cost topFootprint

/-- The up quark is anchored to the spacetime manifold alone. -/
theorem up_ledger : up = anchorPoint / η := by
  simp [up, upFootprint, cost]

/-- The down quark carries the manifold anchor plus the internal symmetry weight. -/
theorem down_ledger : down = (anchorPoint + symWeight) / η := by
  simp [down, downFootprint, cost, add_div]

/-- The strange quark is a linear anchor plus the additive double-symmetry drag
`χσ = 2σ`. -/
theorem strange_ledger : strange = (anchorLine + dragSym) / η := by
  simp [strange, strangeFootprint, cost, add_div]

/-- The charm quark is an areal anchor diluted by the `σ − χ` colour dimensions. -/
theorem charm_ledger : charm = anchorArea / (η * colourDim) := by
  simp [charm, charmFootprint, cost]

/-- The bottom quark is an areal anchor plus the boundary-to-symmetry latency leak. -/
theorem bottom_ledger : bottom = (anchorArea + latencyTerm) / η := by
  simp [bottom, bottomFootprint, cost, add_div]

/-- The top quark is a volumetric anchor plus the reciprocal capacity leak
`Δ³/D`. -/
theorem top_ledger : top = anchorVolume + capLeakTerm := by
  simp [top, topFootprint, cost]

/-! ## E8-only enclosures (no measured reference) -/

/-- E8-only enclosure of the up-quark mass, matching the `e8p` catalog interval. -/
theorem up_value : (2.055 : ℝ) < up * me ∧ up * me < (2.062 : ℝ) := by
  rw [up_ledger]
  unfold anchorPoint η
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.overhead_eq]
  norm_num [me, PMSubstrate.SIUnits.electronMassMeV]

/-- E8-only enclosure of the down-quark mass. -/
theorem down_value : (4.623 : ℝ) < down * me ∧ down * me < (4.63 : ℝ) := by
  rw [down_ledger]
  unfold anchorPoint symWeight η
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.overhead_eq]
  norm_num [me, PMSubstrate.SIUnits.electronMassMeV]

/-- E8-only enclosure of the strange-quark mass. -/
theorem strange_value : (93.5 : ℝ) < strange * me ∧ strange * me < (93.58 : ℝ) := by
  rw [strange_ledger]
  unfold anchorLine dragSym η
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.overhead_eq]
  norm_num [me, PMSubstrate.SIUnits.electronMassMeV]

/-- E8-only enclosure of the charm-quark mass. -/
theorem charm_value : (1267.02 : ℝ) < charm * me ∧ charm * me < (1267.48 : ℝ) := by
  rw [charm_ledger]
  unfold anchorArea colourDim η
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.overhead_eq]
  norm_num [me, PMSubstrate.SIUnits.electronMassMeV]

/-- E8-only enclosure of the bottom-quark mass. -/
theorem bottom_value : (4180.9 : ℝ) < bottom * me ∧ bottom * me < (4182.3 : ℝ) := by
  rw [bottom_ledger]
  unfold anchorArea latencyTerm latencyRatio η
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.overhead_eq]
  norm_num [me, PMSubstrate.SIUnits.electronMassMeV]

/-- E8-only enclosure of the top-quark mass. -/
theorem top_value : (172657 : ℝ) < top * me ∧ top * me < (172686 : ℝ) := by
  rw [top_ledger]
  unfold anchorVolume capLeakTerm capLeak
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq]
  norm_num [me, PMSubstrate.SIUnits.electronMassMeV]

/-- The thresholds Paper III orders are these formulas. -/
theorem threshold_match : charm = PMConstants.StrongRunning.mCharm ∧ bottom = PMConstants.StrongRunning.mBottom := by
  rw [charm_ledger, bottom_ledger]
  unfold anchorArea colourDim latencyTerm latencyRatio η PMConstants.StrongRunning.mCharm
    PMConstants.StrongRunning.mBottom PMConstants.overhead
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq,
    PMSubstrate.E8Values.overhead_eq]
  constructor <;> ring

end PMElementaryParticles.QuarkMasses
