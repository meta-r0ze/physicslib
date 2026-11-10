import PMAtoms.Invariants
import PMHadrons.CompositeMasses
import Mathlib.Tactic

/-!
# Link weights from the composite-mass terms

The proton/neutron masses contain `−πD` and `+σ/2`. Those are the same terms used
for the line/ring link weights:

`pp = πD`, `pn = πD − σ/2`, `nn = πD + σ/2`.

This module proves the connection to the actual `CompositeMasses` formulas.
-/

noncomputable section
namespace PMAtoms
open PMHadrons.CompositeMasses

/-- The map term `πD`, the common link weight. -/
def mapWeight : ℝ := Real.pi * (D : ℝ)

/-- The boundary term `σ/2`, the hetero/homo splitting. -/
def boundaryWeight : ℝ := (σ : ℝ) / 2

def ppWeight : ℝ := mapWeight
def pnWeight : ℝ := mapWeight - boundaryWeight
def nnWeight : ℝ := mapWeight + boundaryWeight

theorem ppWeight_eq : ppWeight = Real.pi * 4 := by
  simp [ppWeight, mapWeight, D]

theorem pnWeight_eq : pnWeight = Real.pi * 4 - 5 / 2 := by
  simp [pnWeight, mapWeight, boundaryWeight, D, σ]

theorem nnWeight_eq : nnWeight = Real.pi * 4 + 5 / 2 := by
  simp [nnWeight, mapWeight, boundaryWeight, D, σ]

/-- The proton base is exactly `Δ² − mapWeight − 1/D`. -/
theorem base_eq : base = (Δ : ℝ) ^ 2 - mapWeight - 1 / (D : ℝ) := by
  unfold base mapWeight
  rw [show (PMSubstrate.E8Values.Delta : ℝ) = (Δ : ℝ) from rfl,
    show (PMSubstrate.E8Values.D : ℝ) = (D : ℝ) from rfl]

/-- The neutron mass adds the boundary weight `σ/2` on top of its base. -/
theorem neutron_boundary :
    neutron = base + boundaryWeight + 3 * zTol - zMar := by
  unfold neutron boundaryWeight
  rw [show (PMSubstrate.E8Values.sigma : ℝ) = (σ : ℝ) from rfl,
    show (PMSubstrate.E8Values.chi : ℝ) = (χ : ℝ) from rfl]
  norm_num [σ, χ, PMSubstrate.baseline]

/-- The hetero link is the map weight minus the boundary weight. -/
theorem pnWeight_map : pnWeight = ppWeight - boundaryWeight := rfl

/-- The homo link is the map weight plus the boundary weight. -/
theorem nnWeight_map : nnWeight = ppWeight + boundaryWeight := rfl

end PMAtoms
