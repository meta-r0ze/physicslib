import PMElementaryParticles.SharedUnits
import PMElementaryParticles.QuarkMasses
import PMHadrons.CompositeMasses
import PMSubstrate.E8Values

/-!
# Meson masses as E8 tier ledgers and as six-pillar cell budgets

The mass of a meson composite is its **occupancy cost**: `n` substrate cells, each paying the
full six-pillar budget `α⁻¹`, plus a short E8 residual. `n` is the room the persistent
configuration holds. Units of `m_e`; `α`, `α⁻¹` from `PMElementaryParticles.SharedUnits`.
Every numeral is a canonical `PMSubstrate.E8Values` invariant.

* **Charged pion.** `2α⁻¹` (the two unit charges' cell budget) − `χσ`
  (topological/symmetry product) + `1/(ν−χ)` (chiral leak) + `σ` + `D` −
  `α(σ−χ)/χ` (charge load). `pionPlus_ledger` records the decomposition.

## Six-pillar form

`α⁻¹` is, by definition, the six-pillar budget of one substrate cell:
`PMSubstrate.impedance baseline = Capacity + Map + Protocol + Governor + Toll + Margin`
(`cellBudget_pillars`). Its Toll and Margin terms are the nucleons' `Z_TOL` and `Z_MAR`
(`tollTerm_eq_zTol`, `marginTerm_eq_zMar`). So every meson is

  `mass = n · cellBudget + residual`

with `n = χ` for the pions and `n = σ + χ` for the kaons (`pion0_cells`, `pionPlus_cells`,
`kaon0_cells`, `kaonPlus_cells`). Each meson therefore carries all six pillars, Toll and Margin
included, `n` times. The residuals are short E8 expressions; the charge load `α(σ−χ)/χ` appears
in both charged mesons and in neither neutral one.

**Not constituents minus a budget.** With the current-quark ledger, every hadron is far heavier
than its quarks (`pionPlus_gt_constituents`, `kaonPlus_gt_constituents`,
`proton_gt_constituents`), so a "constituents minus binding" reading would need a negative
binding. Neither the nucleons nor the mesons use it. The nucleons use a different base (`Δ²`)
instead of whole cell budgets.

**Model inputs.** The cell counts `n` and the residual terms are the paper's assignments; no
cost functional selects them. The measured comparison lives in
`tools/e8p/E8PConstants/LeptonMassPulls.lean` and the `CompositeMasses` pulls.
-/

noncomputable section
namespace PMHadrons.MesonMasses
open PMElementaryParticles.SharedUnits
open PMSubstrate.E8Values

/-- Pion: the two unit charges' cell budget `2α⁻¹`. -/
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

/-! ## Six-pillar cell budget -/

/-- One substrate cell's six-pillar budget, `PMSubstrate.impedance` at the E8 parameters. -/
def cellBudget : ℝ := PMSubstrate.impedance PMSubstrate.baseline

/-- `α⁻¹` is the cell budget, by definition. -/
theorem αinv_eq_cellBudget : αinv = cellBudget := rfl

/-- The cell budget is the sum of the six pillar terms. -/
theorem cellBudget_pillars : cellBudget =
    PMSubstrate.capacityTerm PMSubstrate.baseline + PMSubstrate.mapTerm PMSubstrate.baseline +
    PMSubstrate.protocolTerm PMSubstrate.baseline + PMSubstrate.governorTerm PMSubstrate.baseline +
    PMSubstrate.tollTerm PMSubstrate.baseline + PMSubstrate.marginTerm PMSubstrate.baseline := rfl

/-- The cell's Toll term is the nucleons' `Z_TOL`. -/
theorem tollTerm_eq_zTol : PMSubstrate.tollTerm PMSubstrate.baseline = PMHadrons.CompositeMasses.zTol := by
  norm_num [PMSubstrate.tollTerm, PMHadrons.CompositeMasses.zTol, PMSubstrate.baseline,
    PMSubstrate.Parameters.nodeCapacity, PMSubstrate.Parameters.resolution]

/-- The cell's Margin term is the nucleons' `Z_MAR`. -/
theorem marginTerm_eq_zMar : PMSubstrate.marginTerm PMSubstrate.baseline = PMHadrons.CompositeMasses.zMar := by
  norm_num [PMSubstrate.marginTerm, PMHadrons.CompositeMasses.zMar, PMSubstrate.baseline,
    PMSubstrate.Parameters.embeddingLoad, PMSubstrate.Parameters.intrinsicLoad]

/-! ## Mesons as whole cell budgets plus a residual -/

/-- Cell budgets carried by a pion: `χ`. -/
def pionCells : ℝ := (chi : ℝ)
/-- Cell budgets carried by a kaon: `σ + χ`. -/
def kaonCells : ℝ := (sigma : ℝ) + (chi : ℝ)

/-- Charge load `α(σ−χ)/χ`, carried by both charged mesons. -/
def chargeLoad : ℝ := αe * (((sigma : ℝ) - (chi : ℝ)) / (chi : ℝ))

/-- `π⁰` residual: `−σχ + 1/(ν−χ)`. -/
def pion0Residual : ℝ := -((sigma : ℝ) * (chi : ℝ)) + 1 / ((nu : ℝ) - (chi : ℝ))
/-- `π⁺` residual: the `π⁰` residual plus `σ + D` minus the charge load. -/
def pionPlusResidual : ℝ := pion0Residual + (sigma : ℝ) + (D : ℝ) - chargeLoad
/-- `K⁰` residual: `−σ + Dσ − 2π/(ν−χ)`. -/
def kaon0Residual : ℝ :=
  -(sigma : ℝ) + (D : ℝ) * (sigma : ℝ) - 2 * Real.pi / ((nu : ℝ) - (chi : ℝ))
/-- `K⁺` residual: `−σ + Dπ − 1/√2` minus the charge load. -/
def kaonPlusResidual : ℝ :=
  -(sigma : ℝ) + (D : ℝ) * Real.pi - 1 / Real.sqrt 2 - chargeLoad

theorem pionChargeLoad_eq : pionChargeLoad = chargeLoad := rfl

theorem pion0_cells :
    PMHadrons.CompositeMasses.pion0 = pionCells * cellBudget + pion0Residual := by
  rw [← αinv_eq_cellBudget]
  unfold PMHadrons.CompositeMasses.pion0 pionCells pion0Residual
  simp only [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.nu_eq, Nat.cast_ofNat]
  ring

theorem pionPlus_cells : pionPlus = pionCells * cellBudget + pionPlusResidual := by
  rw [← αinv_eq_cellBudget]
  unfold pionPlus pionCoulomb pionTopological pionLeak pionSymmetry pionAnchor pionChargeLoad
    pionCells pionPlusResidual pion0Residual chargeLoad
  simp only [PMSubstrate.E8Values.chi_eq, Nat.cast_ofNat]
  ring

theorem kaon0_cells :
    PMHadrons.CompositeMasses.kaon0 = kaonCells * cellBudget + kaon0Residual := by
  rw [← αinv_eq_cellBudget]
  unfold PMHadrons.CompositeMasses.kaon0 kaonCells kaon0Residual
  simp only [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.D_eq, Nat.cast_ofNat]
  ring

theorem kaonPlus_cells :
    PMHadrons.CompositeMasses.kaonPlus = kaonCells * cellBudget + kaonPlusResidual := by
  rw [← αinv_eq_cellBudget]
  unfold PMHadrons.CompositeMasses.kaonPlus kaonCells kaonPlusResidual chargeLoad
  simp only [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.D_eq, Nat.cast_ofNat]
  ring

/-! ## Hadrons are not constituents minus a binding budget -/

/-- `π⁺ = u d̄` is heavier than its current quarks. -/
theorem pionPlus_gt_constituents :
    PMElementaryParticles.QuarkMasses.up + PMElementaryParticles.QuarkMasses.down < pionPlus := by
  have hu := PMElementaryParticles.QuarkMasses.up_value
  have hd := PMElementaryParticles.QuarkMasses.down_value
  have hp := pionPlus_value
  unfold me at hu hd
  nlinarith [hu.2, hd.2, hp.1]

/-- `K⁺ = u s̄` is heavier than its current quarks. -/
theorem kaonPlus_gt_constituents :
    PMElementaryParticles.QuarkMasses.up + PMElementaryParticles.QuarkMasses.strange <
      PMHadrons.CompositeMasses.kaonPlus := by
  have hu := PMElementaryParticles.QuarkMasses.up_value
  have hs := PMElementaryParticles.QuarkMasses.strange_value
  have hk := PMHadrons.CompositeMasses.kaonPlus_value
  unfold me at hu hs
  nlinarith [hu.2, hs.2, hk.1]

/-- The proton `uud` is heavier than its current quarks. -/
theorem proton_gt_constituents :
    2 * PMElementaryParticles.QuarkMasses.up + PMElementaryParticles.QuarkMasses.down <
      PMHadrons.CompositeMasses.proton := by
  have hu := PMElementaryParticles.QuarkMasses.up_value
  have hd := PMElementaryParticles.QuarkMasses.down_value
  have hp := PMHadrons.CompositeMasses.proton_value
  unfold me at hu hd
  nlinarith [hu.2, hd.2, hp.1]

end PMHadrons.MesonMasses
