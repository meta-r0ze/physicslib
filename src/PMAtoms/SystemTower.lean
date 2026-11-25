import PMHadrons.NucleonBase
import PMHadrons.Nucleon
import Mathlib.Tactic

/-!
# The system tower: each level carries its own six-pillar budget

The mass of a composite is not only the sum of its constituents. Each level —
elementary protocol, nucleon, nucleus, atom — contributes its own CAP/MAP/PRO/
GOV/TOL/MAR budget. The nucleon level is already fixed by
`PMHadrons.CompositeMasses` (`m_p`, `m_n` include all six pillars).

This module makes the tower explicit:

`latticeSum Z N = Z m_p + N m_n + Z m_e`
`boundMass Z N bN bA = latticeSum Z N − bN.contribution − bA.contribution`

so the periodic-table gap is exactly the nucleus-level plus atom-level budget.
The numeric values of those budgets are **not** invented here; they are the
open E8 calculation.
-/

noncomputable section
namespace PMAtoms
open PMHadrons
open PMHadrons.CompositeMasses PMSubstrate.OccupancyCost

/-- Levels of the persistence tower. -/
inductive Level
  | particle | nucleon | nucleus | atom
  deriving DecidableEq, Repr

/-- A level's six-pillar contribution. For the **mass** ledger, toll, margin and
shared links are positive cost magnitudes and are subtracted from the bound mass.
(The α⁻¹ impedance ledger uses different signs; the sign is system-dependent.) -/
structure LevelBudget where
  level : Level
  toll : ℝ := 0
  margin : ℝ := 0
  sharedLinks : ℝ := 0

def LevelBudget.contribution (b : LevelBudget) : ℝ :=
  b.toll + b.margin + b.sharedLinks

/-- The declared electron unit in the legacy lattice sum. The physical
electron footprint must satisfy `ElectronUnit`. -/
def electronEntry : Footprint := { residual := 1 }

def freeFootprint (z n : ℕ) : Footprint :=
  tower [NucleonBase.protonFootprint.scale z, NucleonBase.neutronFootprint.scale n,
    electronEntry.scale z]

/-- Free-constituent lattice sum. -/
abbrev latticeSum (z n : ℕ) : ℝ := cost (freeFootprint z n)

theorem latticeSum_eq_ledger (z n : ℕ) :
    latticeSum z n = (z : ℝ) * proton + (n : ℝ) * neutron + (z : ℝ) * 1 := by
  have he : cost electronEntry = 1 := by simp [electronEntry, cost]
  simp [latticeSum, freeFootprint, cost_tower, ← NucleonBase.proton_eq_cost,
    ← NucleonBase.neutron_eq_cost, he, add_assoc]

/-- The level's binding correction uses the Toll and Margin price units.
The shared-link term remains in the residual. -/
def LevelBudget.footprint (b : LevelBudget) : Footprint :=
  { toll := tollCount (-b.toll)
    margin := marginCount (-b.margin)
    residual := -b.sharedLinks }

theorem LevelBudget.cost_footprint (b : LevelBudget) : cost b.footprint = -b.contribution := by
  simp [LevelBudget.footprint, LevelBudget.contribution, cost]
  ring

def boundFootprint (z n : ℕ) (nucleusBudget atomBudget : LevelBudget) : Footprint :=
  tower [freeFootprint z n, nucleusBudget.footprint, atomBudget.footprint]

/-- Bound mass after the nucleus- and atom-level budgets. -/
abbrev boundMass (z n : ℕ) (nucleusBudget atomBudget : LevelBudget) : ℝ :=
  cost (boundFootprint z n nucleusBudget atomBudget)

theorem boundMass_eq_ledger (z n : ℕ) (bN bA : LevelBudget) :
    boundMass z n bN bA = latticeSum z n - bN.contribution - bA.contribution := by
  simp [boundMass, boundFootprint, latticeSum, cost_tower, LevelBudget.cost_footprint]
  ring

/-- **The periodic-table gap is exactly the nucleus + atom level budget.** -/
theorem gap_eq_level_budgets (z n : ℕ) (bN bA : LevelBudget) :
    latticeSum z n - boundMass z n bN bA = bN.contribution + bA.contribution := by
  rw [boundMass_eq_ledger]
  ring

/-- A nucleus with no level budget is the free lattice sum. -/
theorem boundMass_zero (z n : ℕ) :
    boundMass z n ⟨.nucleus, 0, 0, 0⟩ ⟨.atom, 0, 0, 0⟩ = latticeSum z n := by
  simp [boundMass_eq_ledger, LevelBudget.contribution]

/-- Only the nucleus level is needed when the atom-level mass is negligible. -/
theorem gap_eq_nucleus_budget (z n : ℕ) (bN : LevelBudget) :
    latticeSum z n - boundMass z n bN ⟨.atom, 0, 0, 0⟩ = bN.contribution := by
  rw [gap_eq_level_budgets]
  simp [LevelBudget.contribution]


theorem LevelBudget.contribution_nonneg (b : LevelBudget)
    (ht : 0 ≤ b.toll) (hm : 0 ≤ b.margin) (hs : 0 ≤ b.sharedLinks) :
    0 ≤ b.contribution := by
  unfold LevelBudget.contribution
  linarith

/-- A nonnegative level budget never increases the bound mass. -/
theorem boundMass_le_latticeSum (z n : Nat) (bN bA : LevelBudget)
    (hN : 0 ≤ bN.contribution) (hA : 0 ≤ bA.contribution) :
    boundMass z n bN bA ≤ latticeSum z n := by
  rw [boundMass_eq_ledger]
  linarith

end PMAtoms
