import PMConstants.Values
import PMSubstrate.SIUnits
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Hydrogen readouts from the certified fine-structure constant

`E_n = -α² m_e c²/(2n²)` and `a₀ = ħc/(α m_e c²)`. The electron rest energy
and `ħc` are supplied unit inputs; the only E8 content is the certified
enclosure of `α`.
-/

noncomputable section
namespace PMAtoms
open PMConstants

/-- Electron rest energy in eV (CODATA 2022), a supplied unit input (`PMSubstrate.SIUnits`). -/
def electronMassEV : ℝ := PMSubstrate.SIUnits.electronMassEV

/-- `ħc` in eV·Å, exact in the SI (`PMSubstrate.SIUnits`). -/
def hbarCEVAngstrom : ℝ := PMSubstrate.SIUnits.hbarcEVAngstrom

/-- Rydberg energy `α² m_e c²/2` in the same units as `me`. -/
def rydbergEnergy (α me : ℝ) : ℝ := α ^ 2 * me / 2

/-- Bohr radius `ħc/(α m_e c²)` in the same units as `hbarc`/`me`. -/
def bohrRadius (α me hbarc : ℝ) : ℝ := hbarc / (α * me)

/-- Hydrogen level `E_n = -R/n²`. -/
def hydrogenLevel (α me : ℝ) (n : ℕ) : ℝ := -rydbergEnergy α me / (n : ℝ) ^ 2

/-- Rydberg energy in eV. -/
def rydbergEV : ℝ := rydbergEnergy Values.alpha electronMassEV

/-- Bohr radius in Å. -/
def bohrRadiusAngstrom : ℝ := bohrRadius Values.alpha electronMassEV hbarCEVAngstrom

/-- `R = m_e/(2(α⁻¹)²)` with the certified `α⁻¹ = geometricIndex` (20-digit enclosure). -/
theorem rydbergEV_bounds :
    (13.6056931158 : ℝ) < rydbergEV ∧ rydbergEV < 13.6056931159 := by
  have hG := PMSubstrate.geometricIndex_bounds
  have hz : 0 < PMSubstrate.geometricIndex := by linarith [hG.1]
  have hne : PMSubstrate.geometricIndex ≠ 0 := hz.ne'
  have heq : rydbergEV = 510998.95069 / (2 * PMSubstrate.geometricIndex ^ 2) := by
    show (1 / PMSubstrate.geometricIndex) ^ 2 * 510998.95069 / 2 = _
    field_simp
  have hsq1 : (137.035999212381397211 : ℝ) ^ 2 < PMSubstrate.geometricIndex ^ 2 :=
    pow_lt_pow_left₀ hG.1 (by norm_num) (by norm_num)
  have hsq2 : PMSubstrate.geometricIndex ^ 2 < (137.035999212381397213 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hG.2 hz.le (by norm_num)
  have h2 : 0 < 2 * PMSubstrate.geometricIndex ^ 2 := by positivity
  rw [heq]
  constructor
  · rw [lt_div_iff₀ h2]; nlinarith [hsq2]
  · rw [div_lt_iff₀ h2]; nlinarith [hsq1]

/-- `a₀ = ħc·α⁻¹/m_e` with the certified `α⁻¹ = geometricIndex`. -/
theorem bohrRadius_bounds :
    (0.5291772106829 : ℝ) < bohrRadiusAngstrom ∧ bohrRadiusAngstrom < 0.5291772106830 := by
  have hG := PMSubstrate.geometricIndex_bounds
  have hz : 0 < PMSubstrate.geometricIndex := by linarith [hG.1]
  have hne : PMSubstrate.geometricIndex ≠ 0 := hz.ne'
  have heq : bohrRadiusAngstrom =
      1973.269804593024659 * PMSubstrate.geometricIndex / 510998.95069 := by
    show 1973.269804593024659 / ((1 / PMSubstrate.geometricIndex) * 510998.95069) = _
    field_simp
  rw [heq]
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith [hG.1]
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith [hG.2]

/-- The `n = 1` level is `-R`. -/
theorem hydrogenLevel_one (α me : ℝ) : hydrogenLevel α me 1 = -rydbergEnergy α me := by
  unfold hydrogenLevel
  norm_num

/-- Every level is the ground-state energy divided by `n²`. -/
theorem hydrogenLevel_ratio (α me : ℝ) (n : ℕ) (_hn : 0 < n) :
    hydrogenLevel α me n = hydrogenLevel α me 1 / (n : ℝ) ^ 2 := by
  rw [hydrogenLevel_one]
  rfl

/-- The ground state is the lowest level. -/
theorem ground_is_lowest {α me : ℝ} (hR : 0 ≤ rydbergEnergy α me) {n : ℕ} (hn : 0 < n) :
    hydrogenLevel α me 1 ≤ hydrogenLevel α me n := by
  rw [hydrogenLevel_one]
  unfold hydrogenLevel
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hle : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hdiv : rydbergEnergy α me / (n : ℝ) ^ 2 ≤ rydbergEnergy α me := by
    rw [div_le_iff₀ hn2]
    simpa [mul_one] using mul_le_mul_of_nonneg_left hle hR
  have hneg : -rydbergEnergy α me / (n : ℝ) ^ 2 =
      -(rydbergEnergy α me / (n : ℝ) ^ 2) := by ring
  rw [hneg]
  exact neg_le_neg hdiv

end PMAtoms
