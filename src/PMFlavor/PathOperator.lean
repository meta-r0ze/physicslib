import PMFlavor.CapacityImpedance
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Concrete path operator

The two path link weights are fixed by the capacity ratio

```
w1 = 1
w2 = pmnsCapacity / ckmCapacity = 21/16.
```

The resulting path operator has rational eigenvalues `0, 9/8, 7/2` and integer
eigenvectors.  This is a structural operator, not a fit to CKM/PMNS.
-/

noncomputable section
namespace PMFlavor.PathOperator

open PMFlavor.TransferFlavor

/-- Capacity-derived path link ratio. -/
def pathLinkRatio : ℝ := pmnsCapacity / ckmCapacity

theorem pathLinkRatio_eq : pathLinkRatio = 21 / 16 := by
  norm_num [pathLinkRatio, pmnsCapacity, ckmCapacity]

/-- Concrete three-channel path operator with `w1=1`, `w2=21/16`. -/
def pathOperator : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, -1, 0;
     -1, 37 / 16, -21 / 16;
     0, -21 / 16, 21 / 16]

def v0 : Fin 3 → ℝ := ![1, 1, 1]
def v1 : Fin 3 → ℝ := ![8, -1, -7]
def v2 : Fin 3 → ℝ := ![2, -5, 3]

theorem pathOperator_mulVec_v0 : pathOperator.mulVec v0 = 0 := by
  funext i
  fin_cases i <;>
    simp [pathOperator, v0, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num

theorem pathOperator_mulVec_v1 : pathOperator.mulVec v1 = (9 / 8 : ℝ) • v1 := by
  funext i
  fin_cases i <;>
    simp [pathOperator, v1, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num

theorem pathOperator_mulVec_v2 : pathOperator.mulVec v2 = (7 / 2 : ℝ) • v2 := by
  funext i
  fin_cases i <;>
    simp [pathOperator, v2, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num

end PMFlavor.PathOperator
