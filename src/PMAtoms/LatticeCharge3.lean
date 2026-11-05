import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import PMAtoms.LatticeCharge

/-!
# Exact `3×3×3` lattice Green function

The first volume-persistent cube (`3×3×3`, one interior vertex) has a rational
Dirichlet Green function with small denominators.  This is the charge geometry
selected by `cube_interior_iff`.
-/

namespace PMAtoms

/-- Exact `3×3×3` Green rows. -/
def green3Rows : List (List Rat) :=
[
  [(353)/(1904), (107)/(2856), (15)/(1904), (107)/(2856), (15)/(952), (1)/(204), (15)/(1904), (1)/(204), (11)/(5712), (107)/(2856), (15)/(952), (1)/(204), (15)/(952), (1)/(102), (11)/(2856), (1)/(204), (11)/(2856), (5)/(2856), (15)/(1904), (1)/(204), (11)/(5712), (1)/(204), (11)/(2856), (5)/(2856), (11)/(5712), (5)/(2856), (5)/(5712)],
  [(107)/(2856), (23)/(119), (107)/(2856), (15)/(952), (121)/(2856), (15)/(952), (1)/(204), (1)/(102), (1)/(204), (15)/(952), (121)/(2856), (15)/(952), (1)/(102), (1)/(51), (1)/(102), (11)/(2856), (19)/(2856), (11)/(2856), (1)/(204), (1)/(102), (1)/(204), (11)/(2856), (19)/(2856), (11)/(2856), (5)/(2856), (1)/(357), (5)/(2856)],
  [(15)/(1904), (107)/(2856), (353)/(1904), (1)/(204), (15)/(952), (107)/(2856), (11)/(5712), (1)/(204), (15)/(1904), (1)/(204), (15)/(952), (107)/(2856), (11)/(2856), (1)/(102), (15)/(952), (5)/(2856), (11)/(2856), (1)/(204), (11)/(5712), (1)/(204), (15)/(1904), (5)/(2856), (11)/(2856), (1)/(204), (5)/(5712), (5)/(2856), (11)/(5712)],
  [(107)/(2856), (15)/(952), (1)/(204), (23)/(119), (121)/(2856), (1)/(102), (107)/(2856), (15)/(952), (1)/(204), (15)/(952), (1)/(102), (11)/(2856), (121)/(2856), (1)/(51), (19)/(2856), (15)/(952), (1)/(102), (11)/(2856), (1)/(204), (11)/(2856), (5)/(2856), (1)/(102), (19)/(2856), (1)/(357), (1)/(204), (11)/(2856), (5)/(2856)],
  [(15)/(952), (121)/(2856), (15)/(952), (121)/(2856), (145)/(714), (121)/(2856), (15)/(952), (121)/(2856), (15)/(952), (1)/(102), (1)/(51), (1)/(102), (1)/(51), (5)/(102), (1)/(51), (1)/(102), (1)/(51), (1)/(102), (11)/(2856), (19)/(2856), (11)/(2856), (19)/(2856), (3)/(238), (19)/(2856), (11)/(2856), (19)/(2856), (11)/(2856)],
  [(1)/(204), (15)/(952), (107)/(2856), (1)/(102), (121)/(2856), (23)/(119), (1)/(204), (15)/(952), (107)/(2856), (11)/(2856), (1)/(102), (15)/(952), (19)/(2856), (1)/(51), (121)/(2856), (11)/(2856), (1)/(102), (15)/(952), (5)/(2856), (11)/(2856), (1)/(204), (1)/(357), (19)/(2856), (1)/(102), (5)/(2856), (11)/(2856), (1)/(204)],
  [(15)/(1904), (1)/(204), (11)/(5712), (107)/(2856), (15)/(952), (1)/(204), (353)/(1904), (107)/(2856), (15)/(1904), (1)/(204), (11)/(2856), (5)/(2856), (15)/(952), (1)/(102), (11)/(2856), (107)/(2856), (15)/(952), (1)/(204), (11)/(5712), (5)/(2856), (5)/(5712), (1)/(204), (11)/(2856), (5)/(2856), (15)/(1904), (1)/(204), (11)/(5712)],
  [(1)/(204), (1)/(102), (1)/(204), (15)/(952), (121)/(2856), (15)/(952), (107)/(2856), (23)/(119), (107)/(2856), (11)/(2856), (19)/(2856), (11)/(2856), (1)/(102), (1)/(51), (1)/(102), (15)/(952), (121)/(2856), (15)/(952), (5)/(2856), (1)/(357), (5)/(2856), (11)/(2856), (19)/(2856), (11)/(2856), (1)/(204), (1)/(102), (1)/(204)],
  [(11)/(5712), (1)/(204), (15)/(1904), (1)/(204), (15)/(952), (107)/(2856), (15)/(1904), (107)/(2856), (353)/(1904), (5)/(2856), (11)/(2856), (1)/(204), (11)/(2856), (1)/(102), (15)/(952), (1)/(204), (15)/(952), (107)/(2856), (5)/(5712), (5)/(2856), (11)/(5712), (5)/(2856), (11)/(2856), (1)/(204), (11)/(5712), (1)/(204), (15)/(1904)],
  [(107)/(2856), (15)/(952), (1)/(204), (15)/(952), (1)/(102), (11)/(2856), (1)/(204), (11)/(2856), (5)/(2856), (23)/(119), (121)/(2856), (1)/(102), (121)/(2856), (1)/(51), (19)/(2856), (1)/(102), (19)/(2856), (1)/(357), (107)/(2856), (15)/(952), (1)/(204), (15)/(952), (1)/(102), (11)/(2856), (1)/(204), (11)/(2856), (5)/(2856)],
  [(15)/(952), (121)/(2856), (15)/(952), (1)/(102), (1)/(51), (1)/(102), (11)/(2856), (19)/(2856), (11)/(2856), (121)/(2856), (145)/(714), (121)/(2856), (1)/(51), (5)/(102), (1)/(51), (19)/(2856), (3)/(238), (19)/(2856), (15)/(952), (121)/(2856), (15)/(952), (1)/(102), (1)/(51), (1)/(102), (11)/(2856), (19)/(2856), (11)/(2856)],
  [(1)/(204), (15)/(952), (107)/(2856), (11)/(2856), (1)/(102), (15)/(952), (5)/(2856), (11)/(2856), (1)/(204), (1)/(102), (121)/(2856), (23)/(119), (19)/(2856), (1)/(51), (121)/(2856), (1)/(357), (19)/(2856), (1)/(102), (1)/(204), (15)/(952), (107)/(2856), (11)/(2856), (1)/(102), (15)/(952), (5)/(2856), (11)/(2856), (1)/(204)],
  [(15)/(952), (1)/(102), (11)/(2856), (121)/(2856), (1)/(51), (19)/(2856), (15)/(952), (1)/(102), (11)/(2856), (121)/(2856), (1)/(51), (19)/(2856), (145)/(714), (5)/(102), (3)/(238), (121)/(2856), (1)/(51), (19)/(2856), (15)/(952), (1)/(102), (11)/(2856), (121)/(2856), (1)/(51), (19)/(2856), (15)/(952), (1)/(102), (11)/(2856)],
  [(1)/(102), (1)/(51), (1)/(102), (1)/(51), (5)/(102), (1)/(51), (1)/(102), (1)/(51), (1)/(102), (1)/(51), (5)/(102), (1)/(51), (5)/(102), (11)/(51), (5)/(102), (1)/(51), (5)/(102), (1)/(51), (1)/(102), (1)/(51), (1)/(102), (1)/(51), (5)/(102), (1)/(51), (1)/(102), (1)/(51), (1)/(102)],
  [(11)/(2856), (1)/(102), (15)/(952), (19)/(2856), (1)/(51), (121)/(2856), (11)/(2856), (1)/(102), (15)/(952), (19)/(2856), (1)/(51), (121)/(2856), (3)/(238), (5)/(102), (145)/(714), (19)/(2856), (1)/(51), (121)/(2856), (11)/(2856), (1)/(102), (15)/(952), (19)/(2856), (1)/(51), (121)/(2856), (11)/(2856), (1)/(102), (15)/(952)],
  [(1)/(204), (11)/(2856), (5)/(2856), (15)/(952), (1)/(102), (11)/(2856), (107)/(2856), (15)/(952), (1)/(204), (1)/(102), (19)/(2856), (1)/(357), (121)/(2856), (1)/(51), (19)/(2856), (23)/(119), (121)/(2856), (1)/(102), (1)/(204), (11)/(2856), (5)/(2856), (15)/(952), (1)/(102), (11)/(2856), (107)/(2856), (15)/(952), (1)/(204)],
  [(11)/(2856), (19)/(2856), (11)/(2856), (1)/(102), (1)/(51), (1)/(102), (15)/(952), (121)/(2856), (15)/(952), (19)/(2856), (3)/(238), (19)/(2856), (1)/(51), (5)/(102), (1)/(51), (121)/(2856), (145)/(714), (121)/(2856), (11)/(2856), (19)/(2856), (11)/(2856), (1)/(102), (1)/(51), (1)/(102), (15)/(952), (121)/(2856), (15)/(952)],
  [(5)/(2856), (11)/(2856), (1)/(204), (11)/(2856), (1)/(102), (15)/(952), (1)/(204), (15)/(952), (107)/(2856), (1)/(357), (19)/(2856), (1)/(102), (19)/(2856), (1)/(51), (121)/(2856), (1)/(102), (121)/(2856), (23)/(119), (5)/(2856), (11)/(2856), (1)/(204), (11)/(2856), (1)/(102), (15)/(952), (1)/(204), (15)/(952), (107)/(2856)],
  [(15)/(1904), (1)/(204), (11)/(5712), (1)/(204), (11)/(2856), (5)/(2856), (11)/(5712), (5)/(2856), (5)/(5712), (107)/(2856), (15)/(952), (1)/(204), (15)/(952), (1)/(102), (11)/(2856), (1)/(204), (11)/(2856), (5)/(2856), (353)/(1904), (107)/(2856), (15)/(1904), (107)/(2856), (15)/(952), (1)/(204), (15)/(1904), (1)/(204), (11)/(5712)],
  [(1)/(204), (1)/(102), (1)/(204), (11)/(2856), (19)/(2856), (11)/(2856), (5)/(2856), (1)/(357), (5)/(2856), (15)/(952), (121)/(2856), (15)/(952), (1)/(102), (1)/(51), (1)/(102), (11)/(2856), (19)/(2856), (11)/(2856), (107)/(2856), (23)/(119), (107)/(2856), (15)/(952), (121)/(2856), (15)/(952), (1)/(204), (1)/(102), (1)/(204)],
  [(11)/(5712), (1)/(204), (15)/(1904), (5)/(2856), (11)/(2856), (1)/(204), (5)/(5712), (5)/(2856), (11)/(5712), (1)/(204), (15)/(952), (107)/(2856), (11)/(2856), (1)/(102), (15)/(952), (5)/(2856), (11)/(2856), (1)/(204), (15)/(1904), (107)/(2856), (353)/(1904), (1)/(204), (15)/(952), (107)/(2856), (11)/(5712), (1)/(204), (15)/(1904)],
  [(1)/(204), (11)/(2856), (5)/(2856), (1)/(102), (19)/(2856), (1)/(357), (1)/(204), (11)/(2856), (5)/(2856), (15)/(952), (1)/(102), (11)/(2856), (121)/(2856), (1)/(51), (19)/(2856), (15)/(952), (1)/(102), (11)/(2856), (107)/(2856), (15)/(952), (1)/(204), (23)/(119), (121)/(2856), (1)/(102), (107)/(2856), (15)/(952), (1)/(204)],
  [(11)/(2856), (19)/(2856), (11)/(2856), (19)/(2856), (3)/(238), (19)/(2856), (11)/(2856), (19)/(2856), (11)/(2856), (1)/(102), (1)/(51), (1)/(102), (1)/(51), (5)/(102), (1)/(51), (1)/(102), (1)/(51), (1)/(102), (15)/(952), (121)/(2856), (15)/(952), (121)/(2856), (145)/(714), (121)/(2856), (15)/(952), (121)/(2856), (15)/(952)],
  [(5)/(2856), (11)/(2856), (1)/(204), (1)/(357), (19)/(2856), (1)/(102), (5)/(2856), (11)/(2856), (1)/(204), (11)/(2856), (1)/(102), (15)/(952), (19)/(2856), (1)/(51), (121)/(2856), (11)/(2856), (1)/(102), (15)/(952), (1)/(204), (15)/(952), (107)/(2856), (1)/(102), (121)/(2856), (23)/(119), (1)/(204), (15)/(952), (107)/(2856)],
  [(11)/(5712), (5)/(2856), (5)/(5712), (1)/(204), (11)/(2856), (5)/(2856), (15)/(1904), (1)/(204), (11)/(5712), (1)/(204), (11)/(2856), (5)/(2856), (15)/(952), (1)/(102), (11)/(2856), (107)/(2856), (15)/(952), (1)/(204), (15)/(1904), (1)/(204), (11)/(5712), (107)/(2856), (15)/(952), (1)/(204), (353)/(1904), (107)/(2856), (15)/(1904)],
  [(5)/(2856), (1)/(357), (5)/(2856), (11)/(2856), (19)/(2856), (11)/(2856), (1)/(204), (1)/(102), (1)/(204), (11)/(2856), (19)/(2856), (11)/(2856), (1)/(102), (1)/(51), (1)/(102), (15)/(952), (121)/(2856), (15)/(952), (1)/(204), (1)/(102), (1)/(204), (15)/(952), (121)/(2856), (15)/(952), (107)/(2856), (23)/(119), (107)/(2856)],
  [(5)/(5712), (5)/(2856), (11)/(5712), (5)/(2856), (11)/(2856), (1)/(204), (11)/(5712), (1)/(204), (15)/(1904), (5)/(2856), (11)/(2856), (1)/(204), (11)/(2856), (1)/(102), (15)/(952), (1)/(204), (15)/(952), (107)/(2856), (11)/(5712), (1)/(204), (15)/(1904), (1)/(204), (15)/(952), (107)/(2856), (15)/(1904), (107)/(2856), (353)/(1904)]
]

def greenCube3 (i j : Fin 27) : Rat :=
  (green3Rows.getD i.val []).getD j.val 0

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

/-- Exact `3×3×3` adjacency. -/
def adj3Rows : List (List Bool) :=
[
  [false, true, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, false, true, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, true, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, false, false, false, true, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, true, false, true, false, true, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, true, false, true, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, true, false, true, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false],
  [true, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false],
  [false, true, false, false, false, false, false, false, false, true, false, true, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false],
  [false, false, true, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false],
  [false, false, false, true, false, false, false, false, false, true, false, false, false, true, false, true, false, false, false, false, false, true, false, false, false, false, false],
  [false, false, false, false, true, false, false, false, false, false, true, false, true, false, true, false, true, false, false, false, false, false, true, false, false, false, false],
  [false, false, false, false, false, true, false, false, false, false, false, true, false, true, false, false, false, true, false, false, false, false, false, true, false, false, false],
  [false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, true, false, false],
  [false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, false, true, false, false, false, false, false, false, false, true, false],
  [false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, true],
  [false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false],
  [false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, true, false, true, false, false, false, false],
  [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false],
  [false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, true, false, true, false, false],
  [false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, false, true, false, true, false],
  [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, false, false, false, true],
  [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, true, false],
  [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, false, true],
  [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, false]
]

def cube3Adj (i j : Fin 27) : Bool :=
  (adj3Rows.getD i.val []).getD j.val false

/-- Dirichlet Laplacian on the `3×3×3` cube. -/
def cube3Lap (f : Fin 27 → Rat) (v : Fin 27) : Rat :=
  6 * f v
    - (if cube3Adj 0 v then f 0 else 0)
    - (if cube3Adj 1 v then f 1 else 0)
    - (if cube3Adj 2 v then f 2 else 0)
    - (if cube3Adj 3 v then f 3 else 0)
    - (if cube3Adj 4 v then f 4 else 0)
    - (if cube3Adj 5 v then f 5 else 0)
    - (if cube3Adj 6 v then f 6 else 0)
    - (if cube3Adj 7 v then f 7 else 0)
    - (if cube3Adj 8 v then f 8 else 0)
    - (if cube3Adj 9 v then f 9 else 0)
    - (if cube3Adj 10 v then f 10 else 0)
    - (if cube3Adj 11 v then f 11 else 0)
    - (if cube3Adj 12 v then f 12 else 0)
    - (if cube3Adj 13 v then f 13 else 0)
    - (if cube3Adj 14 v then f 14 else 0)
    - (if cube3Adj 15 v then f 15 else 0)
    - (if cube3Adj 16 v then f 16 else 0)
    - (if cube3Adj 17 v then f 17 else 0)
    - (if cube3Adj 18 v then f 18 else 0)
    - (if cube3Adj 19 v then f 19 else 0)
    - (if cube3Adj 20 v then f 20 else 0)
    - (if cube3Adj 21 v then f 21 else 0)
    - (if cube3Adj 22 v then f 22 else 0)
    - (if cube3Adj 23 v then f 23 else 0)
    - (if cube3Adj 24 v then f 24 else 0)
    - (if cube3Adj 25 v then f 25 else 0)
    - (if cube3Adj 26 v then f 26 else 0)

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_0 :
    cube3Lap (fun i => greenCube3 i 0) = fun v => if v = 0 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_1 :
    cube3Lap (fun i => greenCube3 i 1) = fun v => if v = 1 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_2 :
    cube3Lap (fun i => greenCube3 i 2) = fun v => if v = 2 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_3 :
    cube3Lap (fun i => greenCube3 i 3) = fun v => if v = 3 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_4 :
    cube3Lap (fun i => greenCube3 i 4) = fun v => if v = 4 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_5 :
    cube3Lap (fun i => greenCube3 i 5) = fun v => if v = 5 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_6 :
    cube3Lap (fun i => greenCube3 i 6) = fun v => if v = 6 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_7 :
    cube3Lap (fun i => greenCube3 i 7) = fun v => if v = 7 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_8 :
    cube3Lap (fun i => greenCube3 i 8) = fun v => if v = 8 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_9 :
    cube3Lap (fun i => greenCube3 i 9) = fun v => if v = 9 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_10 :
    cube3Lap (fun i => greenCube3 i 10) = fun v => if v = 10 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_11 :
    cube3Lap (fun i => greenCube3 i 11) = fun v => if v = 11 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_12 :
    cube3Lap (fun i => greenCube3 i 12) = fun v => if v = 12 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_13 :
    cube3Lap (fun i => greenCube3 i 13) = fun v => if v = 13 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_14 :
    cube3Lap (fun i => greenCube3 i 14) = fun v => if v = 14 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_15 :
    cube3Lap (fun i => greenCube3 i 15) = fun v => if v = 15 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_16 :
    cube3Lap (fun i => greenCube3 i 16) = fun v => if v = 16 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_17 :
    cube3Lap (fun i => greenCube3 i 17) = fun v => if v = 17 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_18 :
    cube3Lap (fun i => greenCube3 i 18) = fun v => if v = 18 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_19 :
    cube3Lap (fun i => greenCube3 i 19) = fun v => if v = 19 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_20 :
    cube3Lap (fun i => greenCube3 i 20) = fun v => if v = 20 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_21 :
    cube3Lap (fun i => greenCube3 i 21) = fun v => if v = 21 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_22 :
    cube3Lap (fun i => greenCube3 i 22) = fun v => if v = 22 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_23 :
    cube3Lap (fun i => greenCube3 i 23) = fun v => if v = 23 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_24 :
    cube3Lap (fun i => greenCube3 i 24) = fun v => if v = 24 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_25 :
    cube3Lap (fun i => greenCube3 i 25) = fun v => if v = 25 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

set_option maxHeartbeats 1000000 in
theorem cube3Lap_green_26 :
    cube3Lap (fun i => greenCube3 i 26) = fun v => if v = 26 then 1 else 0 := by
  funext v
  fin_cases v <;> norm_num [cube3Lap, cube3Adj, greenCube3, green3Rows, adj3Rows]

theorem cube3Lap_green (j : Fin 27) :
    cube3Lap (fun i => greenCube3 i j) = fun v => if v = j then 1 else 0 := by
  fin_cases j
  · exact cube3Lap_green_0
  · exact cube3Lap_green_1
  · exact cube3Lap_green_2
  · exact cube3Lap_green_3
  · exact cube3Lap_green_4
  · exact cube3Lap_green_5
  · exact cube3Lap_green_6
  · exact cube3Lap_green_7
  · exact cube3Lap_green_8
  · exact cube3Lap_green_9
  · exact cube3Lap_green_10
  · exact cube3Lap_green_11
  · exact cube3Lap_green_12
  · exact cube3Lap_green_13
  · exact cube3Lap_green_14
  · exact cube3Lap_green_15
  · exact cube3Lap_green_16
  · exact cube3Lap_green_17
  · exact cube3Lap_green_18
  · exact cube3Lap_green_19
  · exact cube3Lap_green_20
  · exact cube3Lap_green_21
  · exact cube3Lap_green_22
  · exact cube3Lap_green_23
  · exact cube3Lap_green_24
  · exact cube3Lap_green_25
  · exact cube3Lap_green_26

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_0 (j : Fin 27) :
    greenCube3 0 j = greenCube3 j 0 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_1 (j : Fin 27) :
    greenCube3 1 j = greenCube3 j 1 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_2 (j : Fin 27) :
    greenCube3 2 j = greenCube3 j 2 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_3 (j : Fin 27) :
    greenCube3 3 j = greenCube3 j 3 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_4 (j : Fin 27) :
    greenCube3 4 j = greenCube3 j 4 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_5 (j : Fin 27) :
    greenCube3 5 j = greenCube3 j 5 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_6 (j : Fin 27) :
    greenCube3 6 j = greenCube3 j 6 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_7 (j : Fin 27) :
    greenCube3 7 j = greenCube3 j 7 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_8 (j : Fin 27) :
    greenCube3 8 j = greenCube3 j 8 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_9 (j : Fin 27) :
    greenCube3 9 j = greenCube3 j 9 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_10 (j : Fin 27) :
    greenCube3 10 j = greenCube3 j 10 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_11 (j : Fin 27) :
    greenCube3 11 j = greenCube3 j 11 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_12 (j : Fin 27) :
    greenCube3 12 j = greenCube3 j 12 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_13 (j : Fin 27) :
    greenCube3 13 j = greenCube3 j 13 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_14 (j : Fin 27) :
    greenCube3 14 j = greenCube3 j 14 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_15 (j : Fin 27) :
    greenCube3 15 j = greenCube3 j 15 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_16 (j : Fin 27) :
    greenCube3 16 j = greenCube3 j 16 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_17 (j : Fin 27) :
    greenCube3 17 j = greenCube3 j 17 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_18 (j : Fin 27) :
    greenCube3 18 j = greenCube3 j 18 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_19 (j : Fin 27) :
    greenCube3 19 j = greenCube3 j 19 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_20 (j : Fin 27) :
    greenCube3 20 j = greenCube3 j 20 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_21 (j : Fin 27) :
    greenCube3 21 j = greenCube3 j 21 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_22 (j : Fin 27) :
    greenCube3 22 j = greenCube3 j 22 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_23 (j : Fin 27) :
    greenCube3 23 j = greenCube3 j 23 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_24 (j : Fin 27) :
    greenCube3 24 j = greenCube3 j 24 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_25 (j : Fin 27) :
    greenCube3 25 j = greenCube3 j 25 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_symm_26 (j : Fin 27) :
    greenCube3 26 j = greenCube3 j 26 := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

theorem greenCube3_symm (i j : Fin 27) : greenCube3 i j = greenCube3 j i := by
  fin_cases i
  · exact greenCube3_symm_0 j
  · exact greenCube3_symm_1 j
  · exact greenCube3_symm_2 j
  · exact greenCube3_symm_3 j
  · exact greenCube3_symm_4 j
  · exact greenCube3_symm_5 j
  · exact greenCube3_symm_6 j
  · exact greenCube3_symm_7 j
  · exact greenCube3_symm_8 j
  · exact greenCube3_symm_9 j
  · exact greenCube3_symm_10 j
  · exact greenCube3_symm_11 j
  · exact greenCube3_symm_12 j
  · exact greenCube3_symm_13 j
  · exact greenCube3_symm_14 j
  · exact greenCube3_symm_15 j
  · exact greenCube3_symm_16 j
  · exact greenCube3_symm_17 j
  · exact greenCube3_symm_18 j
  · exact greenCube3_symm_19 j
  · exact greenCube3_symm_20 j
  · exact greenCube3_symm_21 j
  · exact greenCube3_symm_22 j
  · exact greenCube3_symm_23 j
  · exact greenCube3_symm_24 j
  · exact greenCube3_symm_25 j
  · exact greenCube3_symm_26 j


/-- General charge energy on the `3×3×3` cube. -/
def latticeChargeEnergy3 (q : Fin 27 → Rat) : Rat :=
  ∑ i, ∑ j, q i * q j * greenCube3 i j

theorem latticeChargeEnergy3_zero : latticeChargeEnergy3 (fun _ => 0) = 0 := by
  simp [latticeChargeEnergy3]

end PMAtoms