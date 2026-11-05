import PMAtoms.LatticeCharge3
import Mathlib.Tactic

/-!
# Charge-energy consequences on the `3×3×3` cube

Lightweight consequences of the exact `3×3×3` Green function, kept in a separate
module so the large finite-check table does not rebuild during iteration.
-/

namespace PMAtoms

/-- A single unit charge has energy `G(i,i)`. -/
theorem latticeChargeEnergy3_single (i : Fin 27) :
    latticeChargeEnergy3 (fun k => if k = i then 1 else 0) = greenCube3 i i := by
  unfold latticeChargeEnergy3
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

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_0 (j : Fin 27) : 0 ≤ greenCube3 0 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_1 (j : Fin 27) : 0 ≤ greenCube3 1 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_2 (j : Fin 27) : 0 ≤ greenCube3 2 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_3 (j : Fin 27) : 0 ≤ greenCube3 3 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_4 (j : Fin 27) : 0 ≤ greenCube3 4 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_5 (j : Fin 27) : 0 ≤ greenCube3 5 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_6 (j : Fin 27) : 0 ≤ greenCube3 6 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_7 (j : Fin 27) : 0 ≤ greenCube3 7 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_8 (j : Fin 27) : 0 ≤ greenCube3 8 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_9 (j : Fin 27) : 0 ≤ greenCube3 9 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_10 (j : Fin 27) : 0 ≤ greenCube3 10 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_11 (j : Fin 27) : 0 ≤ greenCube3 11 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_12 (j : Fin 27) : 0 ≤ greenCube3 12 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_13 (j : Fin 27) : 0 ≤ greenCube3 13 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_14 (j : Fin 27) : 0 ≤ greenCube3 14 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_15 (j : Fin 27) : 0 ≤ greenCube3 15 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_16 (j : Fin 27) : 0 ≤ greenCube3 16 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_17 (j : Fin 27) : 0 ≤ greenCube3 17 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_18 (j : Fin 27) : 0 ≤ greenCube3 18 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_19 (j : Fin 27) : 0 ≤ greenCube3 19 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_20 (j : Fin 27) : 0 ≤ greenCube3 20 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_21 (j : Fin 27) : 0 ≤ greenCube3 21 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_22 (j : Fin 27) : 0 ≤ greenCube3 22 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_23 (j : Fin 27) : 0 ≤ greenCube3 23 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_24 (j : Fin 27) : 0 ≤ greenCube3 24 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_25 (j : Fin 27) : 0 ≤ greenCube3 25 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

set_option maxHeartbeats 1000000 in
theorem greenCube3_nonneg_26 (j : Fin 27) : 0 ≤ greenCube3 26 j := by
  fin_cases j <;> norm_num [greenCube3, green3Rows]

theorem greenCube3_nonneg (i j : Fin 27) : 0 ≤ greenCube3 i j := by
  fin_cases i
  · exact greenCube3_nonneg_0 j
  · exact greenCube3_nonneg_1 j
  · exact greenCube3_nonneg_2 j
  · exact greenCube3_nonneg_3 j
  · exact greenCube3_nonneg_4 j
  · exact greenCube3_nonneg_5 j
  · exact greenCube3_nonneg_6 j
  · exact greenCube3_nonneg_7 j
  · exact greenCube3_nonneg_8 j
  · exact greenCube3_nonneg_9 j
  · exact greenCube3_nonneg_10 j
  · exact greenCube3_nonneg_11 j
  · exact greenCube3_nonneg_12 j
  · exact greenCube3_nonneg_13 j
  · exact greenCube3_nonneg_14 j
  · exact greenCube3_nonneg_15 j
  · exact greenCube3_nonneg_16 j
  · exact greenCube3_nonneg_17 j
  · exact greenCube3_nonneg_18 j
  · exact greenCube3_nonneg_19 j
  · exact greenCube3_nonneg_20 j
  · exact greenCube3_nonneg_21 j
  · exact greenCube3_nonneg_22 j
  · exact greenCube3_nonneg_23 j
  · exact greenCube3_nonneg_24 j
  · exact greenCube3_nonneg_25 j
  · exact greenCube3_nonneg_26 j

theorem latticeChargeEnergy3_nonneg (q : Fin 27 → Rat) (hq : ∀ i, 0 ≤ q i) :
    0 ≤ latticeChargeEnergy3 q := by
  unfold latticeChargeEnergy3
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (hq i) (hq j)) (greenCube3_nonneg i j)


set_option maxHeartbeats 4000000 in
theorem latticeChargeEnergy3_one :
    latticeChargeEnergy3 (fun _ => 1) = 743 / 51 := by
  unfold latticeChargeEnergy3
  simp only [one_mul]
  simp [Fin.sum_univ_succ]
  norm_num [greenCube3, green3Rows]


/-- Uniform fractional charge on the `3×3×3` cube. -/
def uniformCharge3 (q : Rat) : Fin 27 → Rat := fun _ => q

theorem latticeChargeEnergy3_uniform (q : Rat) :
    latticeChargeEnergy3 (uniformCharge3 q) = q * q * (743 / 51) := by
  unfold latticeChargeEnergy3 uniformCharge3
  calc
    (∑ i, ∑ j, q * q * greenCube3 i j)
        = ∑ i, q * q * (∑ j, greenCube3 i j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = q * q * (∑ i, ∑ j, greenCube3 i j) := by
          rw [Finset.mul_sum]
    _ = q * q * (743 / 51) := by
          have h := latticeChargeEnergy3_one
          unfold latticeChargeEnergy3 at h
          simp only [one_mul] at h
          rw [h]

end PMAtoms
