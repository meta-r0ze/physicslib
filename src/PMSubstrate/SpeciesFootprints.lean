import PMSubstrate.OccupancyCost
import PMSubstrate.E8Values

/-!
# Charged lepton and quark footprints

These are the declared occupancy ledgers. Their costs are in electron units.
Use the same footprints for particle values and for thresholds in the running law.
A non-integral region count contributes its whole part to events. Its remaining part
stays in the residual.
-/

noncomputable section
namespace PMSubstrate.SpeciesFootprints
open PMSubstrate.E8Values PMSubstrate.OccupancyCost

namespace Lepton

/-! ## Tier ledgers -/

/-- Muon (Tier 1, line): sweep through the internal symmetry. -/
def muonSweep : ℝ := (Delta : ℝ) * (sigma : ℝ)
/-- Muon: topological anchor. -/
def muonAnchor : ℝ := (chi : ℝ)
/-- Muon: double-cover spin phase lag. -/
def muonSpinLag : ℝ := 2 * Real.pi
/-- Muon: vacuum feedback load `(χ+σ)·α/(1−α)`. -/
def muonFeedback : ℝ := ((chi + sigma : ℕ) : ℝ) * PMSubstrate.causalCoupling / (1 - PMSubstrate.causalCoupling)

/-- The declared line footprint holds `σΔ` clock events. -/
def muonFootprint : Footprint :=
  { events := sigma * Delta
    map := -1
    residual := -muonSpinLag + muonFeedback }

/-- [Premise] Muon mass in `m_e` units in the declared species ledger. -/
abbrev muon : ℝ := cost muonFootprint

/-- The muon is exactly the sum of its named tier costs. -/
theorem muon_ledger :
    muon = (Delta : ℝ) * (sigma : ℝ) - (chi : ℝ) - 2 * Real.pi +
      ((chi + sigma : ℕ) : ℝ) * PMSubstrate.causalCoupling / (1 - PMSubstrate.causalCoupling) := by
  norm_num [muon, muonFootprint, cost, muonSpinLag, muonFeedback,
    PMSubstrate.mapTerm, PMSubstrate.baseline, chi_eq]
  ring

/-- **The feedback load is the recursive loop's fixed point.** The total load of the
admittance ladder `x = (χ+σ)α + α·x` is `(χ+σ)α/(1−α)`. -/
theorem muonFeedback_fixpoint (hα : PMSubstrate.causalCoupling ≠ 1) :
    muonFeedback = ((chi + sigma : ℕ) : ℝ) * PMSubstrate.causalCoupling + PMSubstrate.causalCoupling * muonFeedback := by
  have h : 1 - PMSubstrate.causalCoupling ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  unfold muonFeedback
  field_simp
  ring

/-- Tau (Tier 2, area): boundary cost over the causal area. -/
def tauBoundary : ℝ := (chi : ℝ) * (Delta : ℝ) ^ 2
/-- Tau: inherited linear core latency. -/
def tauCoreLatency : ℝ := (sigma : ℝ) * (Delta : ℝ)
/-- Tau: spacetime anchors. -/
def tauAnchors : ℝ := (D : ℝ) + (chi : ℝ)

/-- The area footprint holds `χΔ² − σΔ` clock events and deducts one Map charge. -/
def tauFootprint : Footprint :=
  { events := chi * Delta ^ 2 - sigma * Delta
    map := -1
    residual := -(D : ℝ) }

/-- [Premise] Tau mass in `m_e` units in the declared species ledger. -/
def tau : ℝ := cost tauFootprint

/-- The tau is exactly the sum of its named tier costs. -/
theorem tau_ledger :
    tau = (chi : ℝ) * (Delta : ℝ) ^ 2 - (sigma : ℝ) * (Delta : ℝ) -
      ((D : ℝ) + (chi : ℝ)) := by
  have count_cost (n : ℕ) :
      cost { events := n, map := -1, residual := -(D : ℝ) } =
        (n : ℝ) - (chi : ℝ) - (D : ℝ) := by
    have hm : PMSubstrate.mapTerm PMSubstrate.baseline = (chi : ℝ) := rfl
    simp [cost, hm, sub_eq_add_neg]
  have h : sigma * Delta ≤ chi * Delta ^ 2 := by
    rw [sigma_eq, Delta_eq, chi_eq]
    omega
  unfold tau tauFootprint
  rw [count_cost, Nat.cast_sub h, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
  ring

end Lepton

namespace Quark

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

/-! The event field is the whole part of the leading term after overhead
and, for charm, colour dilution. The residual keeps its fractional part
and the remaining ledger charges. For top, take the whole part of
`Δ³(D + 1/D)`, its full leading term. These splits preserve the declared
formulas. The occupied regions still need to be derived. -/

def upFootprint : Footprint :=
  let leading := anchorPoint / η
  let whole := ⌊leading⌋₊
  { events := whole, residual := leading - whole }

def downFootprint : Footprint :=
  let leading := anchorPoint / η
  let whole := ⌊leading⌋₊
  { events := whole, residual := leading - whole + symWeight / η }

def strangeFootprint : Footprint :=
  let leading := anchorLine / η
  let whole := ⌊leading⌋₊
  { events := whole, residual := leading - whole + dragSym / η }

def charmFootprint : Footprint :=
  let leading := anchorArea / (η * colourDim)
  let whole := ⌊leading⌋₊
  { events := whole, residual := leading - whole }

def bottomFootprint : Footprint :=
  let leading := anchorArea / η
  let whole := ⌊leading⌋₊
  { events := whole, residual := leading - whole + latencyTerm / η }

def topFootprint : Footprint :=
  let leading := anchorVolume + capLeakTerm
  let whole := ⌊leading⌋₊
  { events := whole, residual := leading - whole }

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
  ring

/-- The strange quark is a linear anchor plus the additive double-symmetry drag
`χσ = 2σ`. -/
theorem strange_ledger : strange = (anchorLine + dragSym) / η := by
  simp [strange, strangeFootprint, cost, add_div]
  ring

/-- The charm quark is an areal anchor diluted by the `σ − χ` colour dimensions. -/
theorem charm_ledger : charm = anchorArea / (η * colourDim) := by
  simp [charm, charmFootprint, cost]

/-- The bottom quark is an areal anchor plus the boundary-to-symmetry latency leak. -/
theorem bottom_ledger : bottom = (anchorArea + latencyTerm) / η := by
  simp [bottom, bottomFootprint, cost, add_div]
  ring

/-- The top quark is a volumetric anchor plus the reciprocal capacity leak
`Δ³/D`. -/
theorem top_ledger : top = anchorVolume + capLeakTerm := by
  simp [top, topFootprint, cost]

end Quark

end PMSubstrate.SpeciesFootprints
