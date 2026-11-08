import PMFlavor.HierarchicalPathOperator

/-! **Experimental/candidate module.**

# Separate PMNS mass operator

The PMNS sector uses a different wall-mass diagonal: the two-wall masses at
`δ = 1`, `y = 1`, with a degenerate light pair and one heavy entry.

This is not the CKM diagonal.
-/

noncomputable section
namespace PMFlavor.PMNSMassOperator

open PMFlavor.PathOperator PMFlavor.HierarchicalPathOperator

/-- Light two-wall mass squared at `δ=1`, `y=1`. -/
def pmnsMassLowSq : ℝ := PMAction.WallDispersion.massSqM 1 1

/-- Heavy two-wall mass squared at `δ=1`, `y=1`. -/
def pmnsMassHighSq : ℝ := PMAction.WallDispersion.massSqP 1 1

/-- Separate PMNS mass operator: degenerate light pair plus heavy entry. -/
def pmnsMassOperator : Matrix (Fin 3) (Fin 3) ℝ :=
  pathOperator + Matrix.diagonal ![pmnsMassLowSq, pmnsMassLowSq, pmnsMassHighSq]

theorem pmnsMassOperator_eq :
    pmnsMassOperator = PMFlavor.HierarchicalPathOperator.HierarchicalOperator pmnsMassLowSq pmnsMassLowSq pmnsMassHighSq := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pmnsMassOperator, PMFlavor.HierarchicalPathOperator.HierarchicalOperator, pathOperator, Matrix.diagonal,
      pmnsMassLowSq, pmnsMassHighSq]

end PMFlavor.PMNSMassOperator
