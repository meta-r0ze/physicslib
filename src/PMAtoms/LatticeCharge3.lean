import Mathlib.Tactic
import PMAtoms.LatticeCharge
import PMAction.CubeGreen3

/-!
# Charge energy on the `3×3×3` cube

The exact Green function of the first volume-persistent cube is `PMAction.LatticeGreen.greenCube3`
(`PMAction.CubeGreen3`). This module keeps its nuclear consequences: two-proton energies,
their sphere calibration, and the general charge energy.
-/

namespace PMAtoms
open PMAction.LatticeGreen

def twoProtonEnergy3 (i j : Fin 27) : Rat :=
  greenCube3 i i + greenCube3 j j + 2 * greenCube3 i j

theorem twoProtonEnergy3_nearest : twoProtonEnergy3 0 1 = 2591 / 5712 := by
  norm_num [twoProtonEnergy3, greenCube3, green3Rows]

theorem twoProtonEnergy3_face : twoProtonEnergy3 0 2 = 46 / 119 := by
  norm_num [twoProtonEnergy3, greenCube3, green3Rows]

theorem twoProtonEnergy3_body : twoProtonEnergy3 0 26 = 19 / 51 := by
  norm_num [twoProtonEnergy3, greenCube3, green3Rows]

theorem twoProtonEnergy3_center : twoProtonEnergy3 13 13 = 44 / 51 := by
  norm_num [twoProtonEnergy3, greenCube3, green3Rows]


/-- Nearest-neighbour calibration for the `3×3×3` cube. -/
noncomputable def latticeNormalization3 : ℝ :=
  sphereCoulomb e8ChargeCoupling 2 27 / (2591 / 5712 : ℝ)

theorem latticeNormalization3_pos : 0 < latticeNormalization3 := by
  unfold latticeNormalization3
  apply div_pos
  · unfold sphereCoulomb
    have hc : 0 < e8ChargeCoupling := e8ChargeCoupling_pos
    have hfac : (0 : ℝ) < (((σ - χ : Nat) : ℝ) / (σ : ℝ)) := by
      rw [sphere_factor]
      norm_num
    have hnum : (0 : ℝ) < (((2 * (2 - 1) : Nat)) : ℝ) := by norm_num
    have hden : 0 < Real.sqrt (((27 : ℝ) ^ ((2 : ℝ) / 3)) + 1) := by
      apply Real.sqrt_pos.mpr
      positivity
    exact div_pos (mul_pos (mul_pos hc hfac) hnum) hden
  · norm_num

noncomputable def normalizedTwoProtonEnergy3 (i j : Fin 27) : ℝ :=
  latticeNormalization3 * (twoProtonEnergy3 i j : ℝ)

theorem normalized_nearest3_eq_sphere :
    normalizedTwoProtonEnergy3 0 1 = sphereCoulomb e8ChargeCoupling 2 27 := by
  unfold normalizedTwoProtonEnergy3 latticeNormalization3
  rw [twoProtonEnergy3_nearest]
  norm_num

theorem normalized_face3_lt_sphere :
    normalizedTwoProtonEnergy3 0 2 < sphereCoulomb e8ChargeCoupling 2 27 := by
  unfold normalizedTwoProtonEnergy3
  rw [twoProtonEnergy3_face]
  norm_num
  have hnorm : 0 < latticeNormalization3 := latticeNormalization3_pos
  have hlt : (46 / 119 : ℝ) < 2591 / 5712 := by norm_num
  have h := mul_lt_mul_of_pos_left hlt hnorm
  calc
    latticeNormalization3 * (46 / 119 : ℝ)
        < latticeNormalization3 * (2591 / 5712 : ℝ) := h
    _ = sphereCoulomb e8ChargeCoupling 2 27 := by
      unfold latticeNormalization3
      field_simp

theorem normalized_body3_lt_sphere :
    normalizedTwoProtonEnergy3 0 26 < sphereCoulomb e8ChargeCoupling 2 27 := by
  unfold normalizedTwoProtonEnergy3
  rw [twoProtonEnergy3_body]
  norm_num
  have hnorm : 0 < latticeNormalization3 := latticeNormalization3_pos
  have hlt : (19 / 51 : ℝ) < 2591 / 5712 := by norm_num
  have h := mul_lt_mul_of_pos_left hlt hnorm
  calc
    latticeNormalization3 * (19 / 51 : ℝ)
        < latticeNormalization3 * (2591 / 5712 : ℝ) := h
    _ = sphereCoulomb e8ChargeCoupling 2 27 := by
      unfold latticeNormalization3
      field_simp

/-- General charge energy on the `3×3×3` cube. -/
def latticeChargeEnergy3 (q : Fin 27 → Rat) : Rat :=
  ∑ i, ∑ j, q i * q j * greenCube3 i j

theorem latticeChargeEnergy3_zero : latticeChargeEnergy3 (fun _ => 0) = 0 := by
  simp [latticeChargeEnergy3]

end PMAtoms
