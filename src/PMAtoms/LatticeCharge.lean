import PMAtoms.LatticeGreen3D
import PMAtoms.NuclearFolding
import Mathlib.Tactic

/-!
# Lattice charge energy

The continuum `sphereCoulomb` is replaced by the exact 3D lattice Green
self-energy on the `2×2×2` cube.  For two unit charges at sites `i,j`:

`E(i,j) = G(i,i) + G(j,j) + 2 G(i,j)`.

The nearest-neighbour pair has `E = 46/105`, below the continuum sphere value.
-/

namespace PMAtoms

/-- Two unit charges on the `2×2×2` cube. -/
def twoProtonEnergy (i j : Fin 8) : Rat :=
  greenCube i i + greenCube j j + 2 * greenCube i j

/-- Nearest-neighbour lattice charge energy. -/
theorem twoProtonEnergy_nearest :
    twoProtonEnergy 0 1 = 46 / 105 := by
  norm_num [twoProtonEnergy, greenCube, greenRows]

/-- Every lattice pair has energy at most the nearest-neighbour value. -/
theorem twoProtonEnergy_le_nearest (i j : Fin 8) (hij : i ≠ j) :
    twoProtonEnergy i j ≤ 46 / 105 := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact (hij rfl).elim
    | norm_num [twoProtonEnergy, greenCube, greenRows]

/-- Symmetry of the lattice pair energy. -/
theorem twoProtonEnergy_symm (i j : Fin 8) :
    twoProtonEnergy i j = twoProtonEnergy j i := by
  unfold twoProtonEnergy
  rw [greenCube_symm i j]
  ring

/-- General lattice charge energy for a rational charge vector. -/
def latticeChargeEnergy (q : Fin 8 → Rat) : Rat :=
  ∑ i, ∑ j, q i * q j * greenCube i j

/-- The lattice charge energy is symmetric under the Green function. -/
theorem latticeChargeEnergy_nonneg (q : Fin 8 → Rat)
    (hq : ∀ i, 0 ≤ q i) : 0 ≤ latticeChargeEnergy q := by
  unfold latticeChargeEnergy
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  have hi := hq i
  have hj := hq j
  have hg : 0 ≤ greenCube i j := by
    fin_cases i <;> fin_cases j <;>
      norm_num [greenCube, greenRows]
  positivity


/-- The lattice nearest-neighbour charge energy is below the continuum sphere. -/
theorem lattice_nearest_lt_sphere :
    (46 / 105 : ℝ) * e8ChargeCoupling < sphereCoulomb e8ChargeCoupling 2 8 := by
  have hc : 0 < e8ChargeCoupling := by
    unfold e8ChargeCoupling
    apply div_pos
    · exact mul_pos Real.pi_pos (by norm_num [D, PMSubstrate.baseline])
    · exact mul_pos (by norm_num) (by norm_num [σ, PMSubstrate.baseline])
  have hsqrt : Real.sqrt 5 < 63 / 23 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hnum : (46 / 105 : ℝ) < 6 / (5 * Real.sqrt 5) := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 5 * Real.sqrt 5)]
    nlinarith
  calc
    (46 / 105 : ℝ) * e8ChargeCoupling
        < (6 / (5 * Real.sqrt 5)) * e8ChargeCoupling :=
          mul_lt_mul_of_pos_right hnum hc
    _ = sphereCoulomb e8ChargeCoupling 2 8 := by
      unfold sphereCoulomb
      rw [show (((σ - χ : Nat) : ℝ) / (σ : ℝ)) = 3 / 5 by exact sphere_factor]
      rw [sphereCoulomb_exponent]
      norm_num
      ring


/-- Unit charges at sites `i` and `j`. -/
def twoCharge (i j : Fin 8) : Fin 8 → Rat :=
  fun k => if k = i then 1 else if k = j then 1 else 0

/-- A single unit charge has energy `G(i,i)`. -/
theorem latticeChargeEnergy_single (i : Fin 8) :
    latticeChargeEnergy (fun k => if k = i then 1 else 0) = greenCube i i := by
  unfold latticeChargeEnergy
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hi
      simp at hi
  · intro j _ hj
    simp [hj]
  · intro hi
    simp at hi

/-- Lattice/continuum charge ratio for the nearest pair. -/
noncomputable def latticeChargeFactor : ℝ :=
  (46 / 105 : ℝ) / (6 / (5 * Real.sqrt 5))

theorem latticeChargeFactor_lt_one : latticeChargeFactor < 1 := by
  unfold latticeChargeFactor
  have hsqrt : Real.sqrt 5 < 63 / 23 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hnum : (46 / 105 : ℝ) < 6 / (5 * Real.sqrt 5) := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 5 * Real.sqrt 5)]
    nlinarith
  exact (div_lt_one (by positivity)).mpr hnum


theorem latticeChargeEnergy_zero : latticeChargeEnergy (fun _ => 0) = 0 := by
  simp [latticeChargeEnergy]

noncomputable def latticeChargeDifference : ℝ :=
  (46 / 105 : ℝ) * e8ChargeCoupling - sphereCoulomb e8ChargeCoupling 2 8

theorem latticeChargeDifference_neg : latticeChargeDifference < 0 := by
  unfold latticeChargeDifference
  have h := lattice_nearest_lt_sphere
  linarith


/-- Nearest-neighbour calibration of the lattice charge to the continuum sphere. -/
noncomputable def latticeNormalization : ℝ :=
  sphereCoulomb e8ChargeCoupling 2 8 / (46 / 105 : ℝ)

theorem e8ChargeCoupling_pos : 0 < e8ChargeCoupling := by
  unfold e8ChargeCoupling
  apply div_pos
  · exact mul_pos Real.pi_pos (by norm_num [D, PMSubstrate.baseline])
  · exact mul_pos (by norm_num) (by norm_num [σ, PMSubstrate.baseline])

theorem latticeNormalization_pos : 0 < latticeNormalization := by
  unfold latticeNormalization
  apply div_pos
  · have hc := e8ChargeCoupling_pos
    have hlat : (0 : ℝ) < (46 / 105) * e8ChargeCoupling :=
      mul_pos (by norm_num) hc
    linarith [lattice_nearest_lt_sphere]
  · norm_num

/-- Calibrated lattice pair energy. -/
noncomputable def normalizedTwoProtonEnergy (i j : Fin 8) : ℝ :=
  latticeNormalization * (twoProtonEnergy i j : ℝ)

theorem normalized_nearest_eq_sphere :
    normalizedTwoProtonEnergy 0 1 = sphereCoulomb e8ChargeCoupling 2 8 := by
  unfold normalizedTwoProtonEnergy latticeNormalization
  rw [twoProtonEnergy_nearest]
  norm_num

theorem twoProtonEnergy_body : twoProtonEnergy 0 7 = 8 / 21 := by
  norm_num [twoProtonEnergy, greenCube, greenRows]

theorem normalized_body_lt_sphere :
    normalizedTwoProtonEnergy 0 7 < sphereCoulomb e8ChargeCoupling 2 8 := by
  unfold normalizedTwoProtonEnergy
  rw [twoProtonEnergy_body]
  norm_num
  have hnorm : 0 < latticeNormalization := latticeNormalization_pos
  have hlt : (8 / 21 : ℝ) < 46 / 105 := by norm_num
  have h := mul_lt_mul_of_pos_left hlt hnorm
  calc
    latticeNormalization * (8 / 21 : ℝ)
        < latticeNormalization * (46 / 105 : ℝ) := h
    _ = sphereCoulomb e8ChargeCoupling 2 8 := by
      unfold latticeNormalization
      field_simp


/-- Finite-size charge differential after nearest-neighbour calibration. -/
noncomputable def latticeChargeDifferential (i j : Fin 8) : ℝ :=
  normalizedTwoProtonEnergy i j - sphereCoulomb e8ChargeCoupling 2 8

theorem latticeChargeDifferential_nearest_zero :
    latticeChargeDifferential 0 1 = 0 := by
  unfold latticeChargeDifferential
  rw [normalized_nearest_eq_sphere]
  ring

theorem latticeChargeDifferential_body_neg :
    latticeChargeDifferential 0 7 < 0 := by
  unfold latticeChargeDifferential
  linarith [normalized_body_lt_sphere]


/-- Continuum sphere with the standard `1/(4π)` Coulomb normalization. -/
noncomputable def sphereCoulombNormalized (z a : Nat) : ℝ :=
  sphereCoulomb e8ChargeCoupling z a / (4 * Real.pi)

theorem sphereCoulombNormalized_nonneg (z a : Nat) :
    0 ≤ sphereCoulombNormalized z a := by
  unfold sphereCoulombNormalized
  exact div_nonneg (sphereCoulomb_nonneg (le_of_lt e8ChargeCoupling_pos) z a) (by positivity)

/-- **The mass-ledger charge term and the standard normalization differ by exactly
`4π`.** The two-ledger mass uses `sphereCoulomb` with the E8 coupling directly
(`chargeTermSphere`), absorbing the `1/(4π)` into its coupling; this makes the
relation explicit rather than a silent convention clash. -/
theorem sphereCoulomb_eq_normalized (z a : Nat) :
    sphereCoulomb e8ChargeCoupling z a =
      4 * Real.pi * sphereCoulombNormalized z a := by
  unfold sphereCoulombNormalized
  rw [mul_div_cancel₀ _ (by positivity : (4 : ℝ) * Real.pi ≠ 0)]

end PMAtoms
